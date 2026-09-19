# Coarse Classes, Hyperdegrees, and the Cone Filter

Research report 10, 18 September 2026. Written in this repository (not delivered as an
archive), as a follow-up to Section 12 of the research plan, "Turing degrees, large countable
ordinals, and large cardinals". Main file: `coarse_hyperdegrees.{tex,pdf}` (10 pages).

## Results

1. **No least hyperdegree (answers direction O1 of the plan, negatively).** For every oracle
   `Z` and every disagreement budget there are sets `A, B`, each Cohen generic over
   `L_{omega_1^Z}[Z]`, with `A symdiff B` obeying the budget, such that
   `Delta^1_1(Z + A)  intersect  Delta^1_1(Z + B) = Delta^1_1(Z)`. Hence there are coarse
   classes with no representative of least hyperdegree, the witnesses having
   `omega_1 = omega_1^CK`, and every hyperdegree is the unattained infimum of the hyperdegree
   spectrum of some coarse class. The proof replaces "the computation converges" by "the
   condition decides the sentence" in the one-bit bridge lemma of the synthesis; the
   partiality case disappears because deciding conditions are dense.
2. **Dyadic codes and the failure of hyperarithmetic compactness (direction O2).** The
   hyperarithmetic core of `R(A)` is exactly `Delta^1_1(A)`, so the classes that refute C1 for
   Turing degrees *do* have least hyperdegrees. Consequently the cone-avoiding compactness
   theorem (HJKS Theorem 3.7) and "gamma(X) = 1 implies trivial core" (HJKS Theorem 4.3) are
   false for hyperarithmetic reducibility. The ordinal `min omega_1^g` over a coarse class
   equals `omega_1^A` for `R(A)`; every countable admissible ordinal occurs.
3. **No cone theorem for coarse degrees (answers direction O4, negatively).** The set of
   functions whose coarse class has a least Turing degree is `Pi^1_1`, invariant under both
   coarse equivalences, and both it and its complement meet every coarse cone. This is a
   theorem of ZF, so Martin's cone theorem has no analogue for the coarse degrees under any
   determinacy hypothesis. Under AD the push-forward of the Martin measure along the block
   code is a countably complete ultrafilter on the nonuniform coarse degrees properly
   extending the cone filter.

## Status

Conventional proofs; not refereed; partly formalized (see "Lean" below); novelty not established. The proof of
result 1 quotes five standard facts (H1)-(H5) about hyperarithmetic sets and Cohen forcing
over `L_{omega_1^CK}` (Feferman 1965; Sacks, *Higher Recursion Theory*, Ch. IV) **from
memory**; they are isolated in Section 2.2 so that they can be checked, and Section 7 says
exactly what is needed from them. Results 2 and 3 depend only on the synthesis
(`../../research-synthesis`) and on Spector's criterion and Sacks's realization theorem.
Remark 4.3 and question (Q1) contain unproved claims and are marked as such.

## Lean

Results 1 and 3 are formalized in the Lean library `CoarseDegrees` at the repository root
(`BudgetForcing.lean`, `Hyper.lean`, `Cone.lean`; see `CoarseDegrees/README.md`). The bridge
lemma in forcing form and the generic-pair construction are proved with nothing admitted.
Theorem 1.1 (for `Z = ∅`) and Corollary 1.2 are derived from two admitted classical facts
(transitivity of hyperarithmetic reducibility, and a package of the facts (H2)-(H5) on Cohen
forcing over `L_{omega_1^CK}`); Theorem 1.5(b), for the nonuniform coarse degrees, from three
(block-code decoding, and the relativizations of HJKS Theorem 4.2 and of the Jockusch-Schupp
remark). Result 2, Corollary 1.3 and the relativization to `Z` are not formalized.

## Build

    latexmk -pdf -interaction=nonstopmode -halt-on-error coarse_hyperdegrees.tex

Same packages as the synthesis (newpx fonts, tcolorbox, enumitem, hyperref).
