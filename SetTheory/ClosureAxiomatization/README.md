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
(batch 143) compares bounded-image, seeded and exact-fiber closure schemas
for a small ZFC-inconsistency search machine. Its new kernels are not
formalized here. The existing `T_iff_ZF` theorem and Foundation-free
forward/reverse components are predecessor results; the report records
their relation and the remaining certification work.
