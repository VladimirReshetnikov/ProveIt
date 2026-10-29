# Guarded Σ₁ formula for the induction-rule case

`ParsonsGuard.guard φ E` forms the actual Foundation semiformula `φ(x) ∨ E`
with `E` lifted over the bound induction variable. For every syntactic term t,
`guard_subst` proves the exact identity `(guard φ E)/[t] = φ/[t] ⋎ E`;
t and E may contain arbitrary free parameters. `guard_sigma` proves the
result is Σ₁ when both inputs are Σ₁. These are syntactic facts, not a
semantic proof of E or a PRA proof.

Two fresh Lean 4.32 builds of the main file and focused checks passed without
warnings, and both objects and complete logs match. The two axiom reports are
limited to `propext`, `Classical.choice`, and `Quot.sound`. The [16-file replay
manifest](parsons-guard-replay/FILES.json) has SHA-256
`5798f0619ea5e45c032e2e1b0c6e5d0712e9c81b2642196cd594b0b1020fe89f`.
The first scratch attempt incorrectly put an unlifted zero-bound formula under
a binder; the second lacked the rewriting-composition identity. Both failed
before the final files were written, and their console logs were not saved.
The successful proof uses `Rew.bShift` and the substitution/composition law.
Existing Foundation/Mathlib compiled objects were inherited; the full
transitive source closure was not rebuilt or audited.

## The rule client remains open

Foundation's `Arithmetic.InductionScheme` is an **axiom scheme**, whereas
Joosten's intermediate theory uses an induction **inference rule**. An actual
proof relation for that intermediate calculus is still needed. One precise
route is an inductive proof relation over open `Proposition L` formulas with:
logical derivations, embedded closed base-theory axioms, modus ponens,
universal generalization/instantiation, and a Σ₁ induction-rule constructor
that takes proofs of the instantiated base and universally quantified step and
returns a proof of the universal conclusion. All proof constructors must remain
finitary and be connected to the existing Foundation LK calculus. A derived
free-variable renaming/substitution theorem must preserve the base theory and
Σ₁ syntactic class; it is essential when generalizing without capturing side
parameters. Alternatively the calculus can use explicit labeled contexts and
prove the equivalent eigenvariable discipline.

The intended guarded-rule theorem must accept actual proof objects for
`φ(0) ⋎ E`, `(∀x (φ(x) → φ(x+1))) ⋎ E`, and `¬φ(t) ⋎ E`, derive both premises
for induction on `guard φ E`, invoke the actual rule, instantiate at t, and
return an actual proof of E. It must not take the guarded step, the final E,
or conservation as an extra assumption. The lemmas here discharge the
membership and binder-substitution parts only. Strict Π₂ prenex conversion,
parameter closure, base-theory membership, the other cut-free induction cases,
and PRA Herbrand/witness extraction are separate obligations.
