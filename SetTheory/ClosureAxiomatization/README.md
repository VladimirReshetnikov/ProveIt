# Closure axiomatization of set theory

The project proves, independently in Lean and Coq, that the theory retaining
Extensionality, Regularity, Separation, and Powerset while replacing Pairing,
Union, Infinity, and Replacement by a single set-like-relation Closure schema
is exactly ZF.

- `Forward` and `Reverse` give self-contained shallow semantic directions.
- `Equivalence` uses the reusable first-order calculus and ZF model theory to
  prove full deductive equivalence.
- [`Article/closure-axiomatization.tex`](Article/closure-axiomatization.tex)
  is the tutorial exposition; the rendered PDF is retained beside it.
- `Research/` retains the provenance transcript for the project's
  genesis.

The Lean development is mathlib-free. Its standalone project is under
[`Lean/`](Lean/); the Coq sources are under [`Coq/`](Coq/).

The external report
[`ZFC closure kernels`](../Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md)
(batches 143–149) compares bounded-image, seeded and exact-fiber closure schemas
for a small ZFC-inconsistency search machine, with a new mathematical
PSC-only hereditary-saturation interpretation and an equivalent empty-input
schema. The reduced numerical C/G calculus has a reviewed finite-sort
countermodel, with an ordinary PA strengthening; this does not refute the
ordinary set-theory interpretation. Complete Hilbert and ground-clause
references are supplied separately from the experimental binary tables.
Later binding-witness and shared-template tableau references implement full
instantiation; a separate 268-state control retains the original complete
logic. Two delivered standalone Lean files check binding syntax and a narrow
PSC/modal obstruction, without verifying either reference checker or its
binary compilation.
These delivery claims are
not formalized in this project; specific subset-PSC results are now checked
in `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PSCCalibration.lean`. The existing `T_iff_ZF` theorem and Foundation-free
forward/reverse components are predecessor results; the report records
their relation and the remaining certification work.
