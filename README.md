# Simple, faster parser for "value terms" in Isabelle.

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

## Example usage

```
value_definition a_big_list :: "int list" where
"[1, 2, 3, 4, 5]"
```

## Shit benchmarks

```
(* 1.23s *)
value_definition foo2 :: "(int\<times>int) list" where
  "[(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), <snip...> (995, 995), (996, 996), (997, 997), (998, 998), (999, 999), (1000, 1000)]"

(* 10s *)
definition foo :: "(int\<times>int) list" where
  "foo = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), <snip...> (995, 995), (996, 996), (997, 997), (998, 998), (999, 999), (1000, 1000)]"
```

See ValueParser_Test.thy for details.

