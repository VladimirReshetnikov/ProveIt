# First-order primitive-recursive function language

`PRALanguage` supplies a Foundation first-order language whose function symbols
are the finite, arity-indexed primitive-recursive codes and whose relations are
Foundation's ordered-ring equality and strict order. It designates zero, one,
addition and multiplication as concrete codes. The `Language.ORing.embedding`
then maps the original ordered-ring symbols to those designated codes. The
language has a computable `Language.Encodable` instance using the code codec.

Lean proves that the designated addition and multiplication codes evaluate to
ordinary addition and multiplication for all natural arguments. A structure
interprets every function symbol by its code evaluator and equality/order by
the ordinary natural relations. `nat_reduct` proves that pulling this structure
back along the embedding is exactly Foundation's standard ordered-ring natural
structure. `nat_formula_map` transfers the semantics of any ordered-ring
formula, with arbitrary free and bound environments, to its language image.
These results are standard-model semantic checks, not object-theory proofs.

The main source and focused checks compiled with Lean 4.32 using
`-M6000 -j1 -DElab.async=false`. Four reported declarations use only the
standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. The private
provider is `/tmp/pra-language-20261029/lib`; snapshots and diagnostics for
all six main attempts and the final checks are in its `logs` directory. The
first two attempts passed narrower code; attempt 3 failed because `fin_cases`
was not imported and also emitted a reducibility warning, attempt 4 repaired
both; attempt 5 failed typeclass inference for language encodability, and
attempt 6 used explicit definitional types. No failed proof was admitted.
The Foundation provider was linked from the hierarchy author's overlay and
Mathlib from the existing cache: this compilation alone does not authenticate
their full current-source transitive dependency closure. Independent replay
and provider verification are separate.

No theory axioms, object-theoretic induction, proof predicate, effective axiom
recognizer, IΣ₁ conservation theorem, or PRA equivalence endpoint is asserted.
