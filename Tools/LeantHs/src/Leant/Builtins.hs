-- | Help for built-ins and keywords that are not constants in the environment
-- (content adapted from the Lean 4 manual and Theorem Proving in Lean 4;
-- port of the BUILTIN_HELP table in leant.py).
module Leant.Builtins
  ( builtinInfo
  ) where

import Data.Char (isSpace)

-- | Help text if the token is a known built-in / keyword.
builtinInfo :: String -> Maybe String
builtinInfo token = lookup canonical builtinHelp
 where
  trimmed = dropWhile isSpace (reverse (dropWhile isSpace (reverse token)))
  canonical = case lookup trimmed aliases of
    Just target -> target
    Nothing -> trimmed

aliases :: [(String, String)]
aliases =
  [ ("->", "\8594"), ("forall", "\8704"), ("exists", "\8707")
  , ("\955", "fun"), ("lambda", "fun")
  , ("<-", "\8592"), ("\10217", "\10216"), ("\10216\10217", "\10216")
  ]

builtinHelp :: [(String, String)]
builtinHelp =
  [ ( "imax"
    , "`imax` is an operation of Lean's built-in *universe level* arithmetic,\n\
      \not a constant in the environment - which is why `#check imax` fails.\n\
      \Universe levels form their own tiny language: `0`, `u+1`, `max u v`,\n\
      \`imax u v`. `imax u v` equals `0` when `v = 0`, and `max u v` otherwise.\n\
      \It appears in the universe of dependent function types:\n\
      \  (x : Sort u) \8594 Sort v  :  Sort (imax u v)\n\
      \so a function into a proposition (`v = 0`) is itself a proposition -\n\
      \this is what makes `Prop` impredicative: `\8704 p : Prop, p : Prop`.\n\
      \Universe expressions can only occur inside `Sort u` / `Type u`."
    )
  , ( "Sort"
    , "`Sort u` is the universe of types at level `u`; it is primitive syntax,\n\
      \not a constant. `Prop` is `Sort 0` and `Type u` is `Sort (u + 1)`.\n\
      \A bare `Sort` needs a level: try `:t Sort 0` or `:t Sort (u + 1)`.\n\
      \Universe levels are built from `0`, `u+1`, `max u v`, `imax u v`."
    )
  , ( "fun"
    , "`fun` (or `\955`) is the keyword introducing an anonymous function; it is\n\
      \syntax, not a constant. Examples:\n\
      \  fun x => x + 1\n\
      \  fun (x : Nat) (y : Nat) => x * y\n\
      \  fun \10216a, b\10217 => a   -- pattern-matching binder\n\
      \`fun x => e : \945 \8594 \946` when `e : \946` given `x : \945`."
    )
  , ( "\8594"
    , "`\8594` (ASCII `->`) is the function arrow, primitive syntax for the\n\
      \(non-dependent) function type - shorthand for `(_ : \945) \8594 \946`. It is\n\
      \right-associative: `\945 \8594 \946 \8594 \947` is `\945 \8594 (\946 \8594 \947)`. The dependent form\n\
      \binds a name: `(x : \945) \8594 p x` (same as `\8704 x : \945, p x`). To inspect it\n\
      \as an operator, apply section notation: `:t (\183 \8594 \183)`."
    )
  , ( "\8704"
    , "`\8704` (keyword `forall`) is the universal quantifier binder. It is\n\
      \notation for the dependent function type: `\8704 x : \945, p x` is exactly\n\
      \`(x : \945) \8594 p x`; a proof of it is a function mapping each `x` to a\n\
      \proof of `p x`. Its universe is `Sort (imax u v)` (see `:info imax`)."
    )
  , ( "\8707"
    , "`\8707` is binder notation for the inductive predicate `Exists`:\n\
      \`\8707 x : \945, p x` unfolds to `Exists fun x => p x`. Introduce it with\n\
      \`\10216witness, proof\10217`, eliminate with `obtain \10216x, hx\10217 := h`.\n\
      \See `:info Exists`."
    )
  , ( "by"
    , "`by` is a keyword that enters *tactic mode*: `by tac` elaborates the\n\
      \tactic block `tac` to produce a term of the expected type, e.g.\n\
      \  theorem t : 2 + 2 = 4 := by rfl\n\
      \It is syntax, not a term - it only makes sense where a term of a known\n\
      \type is expected."
    )
  , ( "do"
    , "`do` is a keyword introducing monadic do-notation: sequencing with\n\
      \`let x \8592 action`, early `return`, `if`/`for`/`try` blocks. A `do` block\n\
      \elaborates to `bind`/`pure` calls in the ambient monad, e.g.\n\
      \  def main : IO Unit := do\n\
      \    let line \8592 (\8592 IO.getStdin).getLine\n\
      \    IO.println line"
    )
  , ( "match"
    , "`match` is the pattern-matching keyword:\n\
      \  match xs with\n\
      \  | []      => ...\n\
      \  | x :: r  => ...\n\
      \It is compiled to auxiliary matcher functions built on recursors, so it\n\
      \is syntax rather than a constant you can `#check`."
    )
  , ( "where"
    , "`where` is a keyword attaching auxiliary definitions to a declaration\n\
      \(visible in its body), and also introduces the field/constructor block\n\
      \of `structure`/`inductive` declarations:\n\
      \  def f (n : Nat) : Nat := g n + 1\n\
      \    where g (k : Nat) := 2 * k"
    )
  , ( "let"
    , "`let` is a keyword introducing a local definition in a term or do-block:\n\
      \`let x := e; body` (or on separate lines). Unlike `fun`-abstraction,\n\
      \`x` is definitionally transparent in `body`."
    )
  , ( "have"
    , "`have` is a keyword stating an intermediate fact in term or tactic\n\
      \mode: `have h : p := proof` makes `h : p` available afterwards. Unlike\n\
      \`let`, the definition is opaque - only the type matters."
    )
  , ( "show"
    , "`show` is a keyword annotating the expected type: `show t from e` (or\n\
      \`show t; tac` in tactic mode) checks/changes the goal to the\n\
      \definitionally equal `t`."
    )
  , ( "calc"
    , "`calc` is the keyword for chained calculational proofs:\n\
      \  calc a = b := by ...\n\
      \       _ = c := by ...\n\
      \Steps are glued with `Trans` instances."
    )
  , ( ":="
    , "`:=` is the definition/assignment token: it separates a declaration's\n\
      \signature from its body (`def f : T := e`), appears in `let`/`have`,\n\
      \and in structure-instance fields (`{ x := 1 }`). It is punctuation, not\n\
      \an operator."
    )
  , ( "=>"
    , "`=>` is the token separating a binder or pattern from its body: in\n\
      \`fun x => e`, in `match` arms (`| pat => e`), and in tactic\n\
      \alternatives. Not to be confused with implication, which is `\8594`."
    )
  , ( "\8592"
    , "`\8592` (ASCII `<-`) is punctuation with two roles: in do-notation,\n\
      \`let x \8592 action` binds the result of a monadic action; inside a do\n\
      \expression `(\8592 action)` inlines it. In `rw [\8592 h]` it rewrites with\n\
      \equation `h` right-to-left."
    )
  , ( "|"
    , "`|` separates alternatives: constructors in `inductive ... where`,\n\
      \arms of `match` (and equation-style `def`), and tactics use\n\
      \`first | t\8321 | t\8322`. `p\8321 | p\8322` inside patterns does not\n\
      \exist in Lean 4 - write separate arms."
    )
  , ( "@"
    , "`@f` is the *explicit application* prefix: it turns all implicit\n\
      \arguments of `f` into explicit ones, e.g. `@id Nat 3`. Useful with\n\
      \`:t @f` to see the full signature including implicits."
    )
  , ( "_"
    , "`_` is a placeholder (hole): Lean infers the term or type from\n\
      \context. In proofs, `?h` named holes create goals; in patterns `_`\n\
      \matches anything without binding a name."
    )
  , ( "\183"
    , "`\183` is the section/placeholder dot: `(\183 + 1)` is `fun x => x + 1`,\n\
      \`(\183 \8594 \183)` is `fun a b => a \8594 b`. Each `\183` inside the closest\n\
      \parentheses becomes a fresh bound variable, in order."
    )
  , ( "\10216"
    , "`\10216e\8321, e\8322, ...\10217` is the *anonymous constructor*: it builds a value of\n\
      \any expected single-constructor type (pairs, `And`, `Exists`,\n\
      \structures): `(\102161, rfl\10217 : \8707 n, n = 1)`. In patterns it destructures."
    )
  ]
