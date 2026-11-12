# Bounded root74 proof-escape token audit

This read-only lexical audit checks all 159 original bare-draft sources, the
31 directly qualified project-source files in the pinned root74 endpoint
inventory, and all 159 inert sources in the pinned root74 slim overlay. The
checker verifies every listed source hash against its pinned inventory.

After removing nested block comments, line comments and ordinary escaped
strings, the checker finds no code-token occurrences of `sorry`, `admit`,
`axiom`, `unsafe`, `native_decide`, `run_tac`, `implemented_by`,
`ofReduceBool`, `trustCompiler`, `partial`, `unsafeCast`, `sorryAx`, `panic!`
or `unreachable!` in any of those three bounded sets. Synthetic controls
exercise every listed token and comment/string suppression. This is a lexical
search, not a Lean parser, proof checker, theorem-axiom report or evidence
that unlisted mechanisms cannot bypass proofs. The scanner explicitly rejects the literal textual patterns `r#"`, `s!"`,
`m!"` and `f!"`, as well as `«`/`»` in code; other Lean literal or identifier
forms may be unhandled. This is not exhaustive detection of Lean syntax.

The direct-qualified set does contain four classical-selection references:
`Classical.choose`/`Classical.choose_spec` in
`ArithmeticAdaptiveFactorUnits2011.lean`, and `Classical.choose!`/
`Classical.choose!_eq_iff_right` in `ArithmeticGcdNormalization.lean`. These
are not `sorry` or a finding of an invalid proof. They show why absence of the
selected escape tokens cannot establish an axiom-free or approved-axiom
closure. The scanner also observes 209 `#print axioms` commands in the bare
set and 52 in the directly qualified set; they are source text only and were
not executed. No axiom output is asserted.

The sets do not include qualified-source transitive imports, Foundation or
package sources, generated definitions, Lean objects/companions, runtime or
provider dependencies. Tactic behavior, theorem elaboration, the exact axiom
closure, model/iPRA endpoint and byte/PDF binding remain unverified. The slim
overlay is inert source, not a built module tree. No Lean run occurred.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary14-root74-proof-escape-audit/check_source.py | cmp - research/ordinary14-root74-proof-escape-audit/observation.json
```

Independent source review: [root74 proof-escape audit](../../reviews/ordinary14-root74-proof-escape-audit-independent/README.md).
