(*
Simple, faster parser for value/const subset of Isabelle terms.

The Isabelle parser does some fancy mixfix stuff, but as a result it's quite complicated.
For some tasks, such as parsing a deep embedding of a moderate-sized program, using the full
parser can be overkill. Then, after we've parsed the term, we need to do full type inference.
These two together can be incredibly slow – a list with a thousand elements can take 7 seconds to
parse and type check.

In cases where we know ahead of time that our definition will only contain a subset of syntactic
 constructs, we don't need the full power of the Isabelle parser. Furthermore, if there are no
binders, and the only functions are relatively simple data constructors, typechecking is much
simpler. With these specialisations, the same list with a thousand elements takes around 0.8s to
parse and type check - about ten times faster than Syntax.read_term.
(This is, of course, still appallingly slow.)


*)

theory ValueParser
  imports Main
begin

ML {*

(* The scanner and parser here are based on Isabelle SIMPLE_SYNTAX:
    https://github.com/seL4/isabelle/blob/master/src/Pure/Syntax/simple_syntax.ML
  The scanner is more or less a direct copy, while the parser is loosely based on the original parser.
 *)
structure ValueParser = struct
local

val lexicon = Scan.make_lexicon
  (map Symbol.explode ["(", ")", "[", "]", ","]);

fun read scan s =
  (case
      Symbol_Pos.explode0 s |>
      Lexicon.tokenize lexicon false |>
      filter Lexicon.is_proper |>
      Scan.read Lexicon.stopper scan of
    SOME x => x
  | NONE => error ("Malformed input: " ^ quote s));


(* basic scanners *)

fun $$ s =
  Scan.some (fn tok =>
    if Lexicon.is_literal tok andalso s = Lexicon.str_of_token tok then SOME s else NONE);

fun kind k =
  Scan.some (fn tok =>
    if Lexicon.kind_of_token tok = k then SOME (Lexicon.str_of_token tok) else NONE);

val ident = kind Lexicon.Ident;
val long_ident = kind Lexicon.Long_Ident;
val num = kind Lexicon.Num :|-- (fn str => case Lexicon.read_int str of SOME i => Scan.succeed i | NONE => raise ERROR ("Lexer failure: token identified as number, but parse failed. Token: " ^ str));
val str = kind Lexicon.Str;

val const = long_ident || ident;

(* value-style terms: nothing fancy *)

fun id_or_const ctxt expectT =
 let
  fun fix_const (Const (a,ty),_) = (Const (a, ty), [])
    | fix_const (t,_) = (t, []) 
  fun lookup i =
    fix_const (Consts.check_const (Context.Proof ctxt) (Proof_Context.consts_of ctxt) (i,[]))
    handle ERROR _ => (Free (i, expectT ()), [])
 in
  const >> lookup
 end

fun comma_sep1 ps =
 let
  fun go xs =
   ps :|-- (fn x =>
      ($$ "," |-- go (x :: xs)) || Scan.succeed (x :: xs)
    )
 in
  go [] :|-- (fn xs => Scan.succeed (rev xs))
 end

fun comma_sep ps =
  comma_sep1 ps || Scan.succeed []

fun mk_string strlit =
 let
  val chop = String.substring (strlit, 2, String.size strlit - 4)
 in
  HOLogic.mk_string chop
 end

(* Parse a value-style term *)
fun term ctxt =
 let
  (* Type variable name supply *)
  val tvar_dummy_ref : int Unsynchronized.ref = Unsynchronized.ref 0
  fun tvar_dummy () = (tvar_dummy_ref := !tvar_dummy_ref + 1; (Term.TVar (("tvar_dummy",!tvar_dummy_ref),dummyS)))

  fun mk_prod (t1,t2) = HOLogic.pair_const (tvar_dummy ()) (tvar_dummy ()) $ t1 $ t2
  fun mk_tuple ts = foldr1 mk_prod ts

  fun mk_num 0 = (Const (@{const_name Groups.zero_class.zero}, tvar_dummy ()))
    | mk_num 1 = (Const (@{const_name Groups.one_class.one}, tvar_dummy ()))
    | mk_num i = (Const (@{const_name Num.numeral_class.numeral},@{typ num} --> tvar_dummy ())) $ HOLogic.mk_numeral i

  fun term1 x = term4 x
  and term4 x =
    (term5 :|--
      (fn hd =>
        Scan.repeat1 term5 >> curry Term.list_comb hd ||
        Scan.succeed hd)) x
  and term5 x =
   (id_or_const ctxt tvar_dummy >> fst ||
    num >> mk_num ||
    str >> mk_string ||
    parse_parens ||
    parse_list
   ) x

  and parse_list x =
    ($$ "[" |-- (comma_sep term1 >> HOLogic.mk_list (tvar_dummy ())) --| $$ "]") x

  and parse_parens x =
    ($$ "(" |-- (term1 :|-- (fn t => ($$ ")" |-- Scan.succeed t) || ($$ "," |-- parse_tuple_elts t --| $$ ")")))) x
  and parse_tuple_elts t =
  comma_sep term1 >> (fn ts => mk_tuple (t :: ts))

 in
  term1
 end

fun read_tm ctxt s =
  let
    val tm = read (term ctxt) s
      handle ERROR msg => cat_error ("Cannot parse input " ^ quote s) msg;
  in
    tm
  end;

in

(* Try to do a trivial type elaboration on the parsed term, given that we know the expected type *)
(* When this works, it's much faster than full-on type inference *)
fun cheap_elaborate_term expectT tm =
 let
  (* Destruct function into domain and range *)
  (* If it's not recognised as a function assume '_' *)
  fun dest_funT (Type ("fun", [t, u])) = (t, u)
    | dest_funT t = (dummyT, t)

  (* Get result type of function type after applying to n arguments *)
  fun dest_funT_nth_range t 0 = t
    | dest_funT_nth_range (Type ("fun", [_, u])) ix = dest_funT_nth_range u (ix - 1)
    | dest_funT_nth_range _ _ = dummyT

  (* We want a value of type 'expectT', and we have a function of type 'funT' that we've applied
     'num_apps' times.
     Unify the result type of applying 'funT' with the expected type 'expectT', then apply that
     unification to the rest of 'funT'. *)
  fun instantiate_return_ty expectT num_apps funT =
    let val res_t = dest_funT_nth_range funT num_apps
        val match_t = Type.raw_unify (res_t, expectT) Vartab.empty
    in Envir.subst_type match_t funT end

 (* If we've finished with our simple instantiation and there are some type variables left over,
    we want to replace them with dummyT '_' so that real type checking can solve them.
    Otherwise, type checking would fall over on the type variable. *)
 fun strip_tvars (Type (t,ts)) = Type (t, map strip_tvars ts)
   | strip_tvars (TFree s)     = TFree s
   | strip_tvars (TVar _)      = dummyT

  (* Recurse over the term, tracking the expected return type.
     We count the number of applications so that we know how many function arrows to unpeel when we
     hit a Const with a function type. *)
  fun go_hd expectT num_apps tm =
    case tm of
      Const (c,t) =>
       if expectT = dummyT
       then (Const (c, strip_tvars t), t)
       else let val t' = instantiate_return_ty expectT num_apps t
            in (Const (c, strip_tvars t'), t') end
    | a $ b =>
       let val (a',t') = go_hd expectT (num_apps + 1) a
           val (tI,tO) = dest_funT t'
           val (b',_)  = go_hd tI 0 b
       in (a' $ b', tO) end
    | Free (v,t_orig) => if num_apps = 0
                         then (Free (v, strip_tvars expectT), expectT)
                         else (Free (v, strip_tvars  t_orig), expectT)
    | Var  (v,t_orig) => if num_apps = 0
                         then (Var  (v, strip_tvars expectT), expectT)
                         else (Var  (v, strip_tvars  t_orig), expectT)
    | Bound _ => (tm, expectT)
    | Abs   _ => (tm, expectT)

  val res = go_hd expectT 0 tm
 in
  fst res
 end

(* Parse and type check term *)
fun read_term ctxt t str =
 let
  val timing = Timing.start ()
  (* Parse *)
  val tm = read_tm ctxt str
  val _ = @{print tracing} "read_tm"
  val _ = @{print tracing} (Timing.result timing)
  val timing = Timing.start ()
  (* Try to elaborate the term with type annotations *)
  val tm = cheap_elaborate_term t tm
  val _ = @{print tracing} "cheap_elaborate_term"
  val _ = @{print tracing} (Timing.result timing)
  val timing = Timing.start ()
  (* Check whether the elaboration worked, or if there are still unknown types around.
     If it didn't finish, we need to fall back to full type checking.
     Really, elaboration could return a boolean saying whether it finished, but this is cheap enough. *)
  val tm = Term.map_types Term.no_dummyT tm
      handle TYPE _ =>
        (@{print warning} "Warning: could not fully infer type of value expression; falling back to type checking";
         @{print warning} tm;
         Syntax.check_term ctxt tm)
  val _ = @{print tracing} "check_term"
  val _ = @{print tracing} (Timing.result timing)
 in tm end

end
end
*}

end