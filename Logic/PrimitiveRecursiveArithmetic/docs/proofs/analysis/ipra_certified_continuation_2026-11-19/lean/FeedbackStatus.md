# Formalization status

`FeedbackReference.lean` is a fully written **uncompiled candidate** over the
ambient Lean rational numbers. No Lean executable or Lake project was available
in this environment. Consequently this delivery does not claim that the file
elaborates or that Lean's kernel has checked any new theorem.

`PolynomialBlueprint.lean` and `FactorBlueprint.lean` are also uncompiled.
They contain executable host-level definitions for the report's actual
polynomial and factor algorithms. Their `ProofObligations` structures are
deliberately not instantiated: the fields name propositions still to prove.
Defining a proposition or a structure containing proof fields proves nothing.

The source contains no `sorry` proofs and introduces no axioms. That is a source-level
fact, not a substitute for compilation. The important remaining gate is a build
against the pinned ProveIt Lean/Mathlib toolchain.

Even a successful build would establish rational semantic lemmas in Lean,
**not** the requested embedded-iPRA endpoints. The separate plan in
`OBJECT_PORT.md` explains the primitive-recursive codes, QF invariants and
object proof obligations needed for those endpoints.

The existing repository modules cited in `OBJECT_PORT.md` were read from
ProveIt commit `3ee850b4c2d650cf01263823fd5415963747c5d0`; their claimed checked
status comes from the repository. They were not rebuilt in this environment.
