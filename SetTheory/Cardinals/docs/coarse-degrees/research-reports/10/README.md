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

## Added 19 September 2026

**Result 4 (Theorem 1.6).** Budgets are closed under intersection, and a set obeys the
*density budget* `|E cap [0,n)| <= r*n` exactly when it is within distance `r` of the empty
set in the prefix-density metric. So a condition of this forcing **is a ball of the metric in
which the synthesis runs its Baire-category arguments**: the two methods act on the same
space. Imposing both constraints at once, the witnesses of result 1 can be taken coarsely
equal *and* within distance `r` for any prescribed `r > 0`, so a hyperdegree minimal pair sits
inside every ball of that metric. Formalized in Lean with nothing admitted beyond what result
1 already uses.

**Question (Q1) analysed, not settled.** (Q1) asks whether the cone `{D : A <=_h D}` is meager
when `A` is outside the hyperarithmetic core. The reduction is sound -- the cone is `Sigma^1_1`,
so it has the Baire property, and finite modifications preserve hyperdegree -- so everything
reduces to "comeager in a ball implies all of the ball". Two routes are now ruled out:

- the Turing proof cannot be repaired, since it runs through the local decoder whose
  conclusion (the robust-radius characterization) is false for `<=_h` by result 2;
- the obvious *forcing* proof is **circular**: one can build a pair inside the ball dodging the
  meager complement, so both coordinates land in the cone and the bridge lemma applies, but the
  ground model must contain the parameters defining the dense sets, and the cone is defined
  from `A` itself. The bridge lemma then says only that `A` is hyperarithmetic in a ground
  model containing `A`. This is the same circularity that makes the classical "hyperarithmetic
  in comeager many implies hyperarithmetic" a theorem about `Sigma^1_1` sets rather than a
  genericity argument.

A third observation: the classical theorem does not transfer along the obvious Cantor-space
parametrization, because `D_X` is nowhere locally compact and so any such image is nowhere
dense. What remains is to run the `Sigma^1_1` category machinery directly in `D_X`.

## What is classical here, and what is not

Minimal pairs of hyperdegrees are **classical**: Feferman (1965) embedded every countable
partial order into the hyperdegrees below `deg_h(O)` by Cohen forcing, Gandy-Sacks (1967)
constructed a minimal hyperdegree (and two distinct minimal hyperdegrees form a minimal
pair), and Thomason (1967) extended the forcing side. For the *unrestricted* product forcing
the minimal-pair property of a mutually generic pair has a one-line proof, and the bridge
lemma of this report degenerates to it.

The whole content of result 1 is therefore the **budget**. Under a budget `(alpha, beta)`
need not be a condition, since the two strings may by then disagree too often, and the
one-bit reserve plus the hybrid path is what restores the comparison. This matters because a
Cohen generic set is at upper density 1 from every hyperarithmetic set: no classical
construction puts a hyperdegree minimal pair inside a *single coarse class*. That combination
is the only thing claimed as possibly new, and it has not been established. Added after a
literature check on 19 September 2026.

## Status

Conventional proofs; not refereed; partly formalized (see "Lean" below). The proof of
result 1 uses five standard facts (H1)-(H5) about hyperarithmetic sets and Cohen forcing
over `L_{omega_1^CK}`, written from memory and isolated in Section 2.2. Verification status
as of 19 September 2026:

- **(H4) confirmed** against Shore, *Lattice initial segments of the hyperdegrees*
  (arXiv:1408.3147), which states for the same Feferman forcing that Cohen genericity
  preserves `omega_1^CK` and that the sets of `M(omega_1^CK, G)` are exactly those
  hyperarithmetic in `G`. (H2) is the standard forcing apparatus of the same source.
- **(H3) not confirmed**, and it must be read carefully: the neighbouring *uniform*
  statement is false, since forcing of `Sigma^1_1` sentences (and of ranked sentences for
  perfect-tree conditions) is `Pi^1_1`, not `Delta^1_1`. What is used, and all that is used,
  is that for one *fixed* ranked formula the forcing relation is `Delta^1_1`. Sacks,
  *Higher Recursion Theory*, III.4 would settle this and should be read before the result is
  relied on. Results 2 and 3 depend only on the synthesis
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
