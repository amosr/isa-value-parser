theory ValueDefinition
  imports Main ValueParser
  keywords "value_definition" :: thy_decl
begin

ML {*
local

fun gen_def binding raw_ty raw_tm int lthy =
  let
    val timing = Timing.start ()
    val ty = Syntax.read_typ lthy raw_ty
    val tm = read_term lthy ty raw_tm
    val tm_with_eq = Const (@{const_name Pure.eq}, ty --> ty --> @{typ prop}) $ Free (Binding.name_of binding, ty) $ tm
    fun get_pos _ = []
    val _ = @{print tracing} "Parsing & type checking"
    val _ = @{print tracing} (Timing.result timing)
    val timing = Timing.start ()
    val (((x, T), rhs), prove) = Local_Defs.derived_def lthy get_pos {conditional = true} tm_with_eq;
    val _ = @{print tracing} "Derived def"
    val _ = @{print tracing} (Timing.result timing)
    val timing = Timing.start ()
    val _ = Name.reject_internal (x, []);
    val (b, mx) = (Binding.make (x, Position.none), NoSyn);
    val name = Thm.def_binding b;
    val _ = @{print tracing} "Def binding"
    val _ = @{print tracing} (Timing.result timing)
    val timing = Timing.start ()
    val ((lhs, (_, raw_th)), lthy2) = lthy
      |> Local_Theory.define_internal ((b, mx), ((Binding.suffix_name "_raw" name, []), rhs));

    val _ = @{print tracing} "define_internal"
    val _ = @{print tracing} (Timing.result timing)
    val timing = Timing.start ()
    val th = prove lthy2 raw_th;
    val _ = @{print tracing} "prove"
    val _ = @{print tracing} (Timing.result timing)
    val timing = Timing.start ()
    val lthy3 = lthy2 |> Spec_Rules.add Spec_Rules.Equational ([lhs], [th]);

    val _ = @{print tracing} "spec_rules"
    val _ = @{print tracing} (Timing.result timing)
    val timing = Timing.start ()
    val ([(def_name, [th'])], lthy4) = lthy3
      |> Local_Theory.notes [((name, []), [([th], [])])];

    val lthy5 = lthy4
      |> Code.declare_default_eqns [(th', true)];

    val lhs' = Morphism.term (Local_Theory.target_morphism lthy5) lhs;

    val _ =
      Proof_Display.print_consts int (Position.thread_data ()) lthy5
        (member (op =) (Term.add_frees lhs' [])) [(x, T)];
    val _ = @{print tracing} "Insert binding"
    val _ = @{print tracing} (Timing.result timing)
  in ((lhs, (def_name, th')), lthy5) end;


val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>value_definition\<close> "constant definition"
    (Parse.binding -- (Parse.$$$ "::" |-- Parse.typ --| Parse.where_ -- Parse.string)
       >> (fn (binding,(typ,term)) =>
          #2 oo gen_def binding typ term));
in end
*}

end