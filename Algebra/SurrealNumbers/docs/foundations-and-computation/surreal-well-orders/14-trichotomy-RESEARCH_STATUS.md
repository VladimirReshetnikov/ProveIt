# Research status and audit

Date: 3 October 2026.

## Foundations

The new class-level results assume GBC (Gödel–Bernays set theory with
Global Choice), canonical set sign-sequence representatives of surreals,
and a fixed class bijection b: Ord -> No. Surreal set-cut existence is a
standard input. The arguments never apply it to proper-class option sets.

The skeleton consists of SET codes; their evaluations are class functions.
A cut of the skeleton is a supplied class parameter. No ordinary class of
all class cuts or of all global class well-orders is formed. Reconstruction
uses elementary class comprehension and set-valued recursion with set
histories, not elementary transfinite recursion choosing classes.

The inaccessible-universe model is a separate illustration requiring a
strongly inaccessible cardinal externally. It is not an extra hypothesis
of the GBC theorems.

## Continuation results proved in writing

- Boundary trichotomy and uniqueness of its parameters.
- Complete character calculation, with normalized principal cuts having
  character (Ord, 1), not (Ord, Ord).
- Exhaustive-cut recognition from crossing prefixes and label coverage;
  coverage alone implies unbounded coherence in this proper-class setting.
- Same-set class-realization absoluteness for old exhaustive trace cuts.
- Complete character invariant for normalized-cut automorphism orbits.
- Noninvariance of exhaustive and branch representability under bare-order
  class automorphisms.
- Support compression, eta_(cf kappa) saturation below a support bound,
  and a sharp omitted configuration whose attained support cost is kappa.
- Exact trace fibers for unrestricted labelled class well-orders.

Historical priority of these extensions has not been established. Some
auxiliary statements and general homogeneity arguments are standard; they
are not described as newly discovered classical theorems.

## Inherited background, explicitly distinguished

The predecessor supplies fixed-alphabet cardinalities and ordinal spectra,
the birthday minimal-slice binary equimorphism, core interpolation and its
surreal order type, global-choice equivalence, direct raw-order comparison,
canonical initial branches, and the diagonal obstruction to exhaustive
uniform coding. Prerequisite arguments are reproved where useful. The
present article does not replace the inherited ordinal-spectrum proof by
a counting argument.

## Targeted repository inspection

Repository: VladimirReshetnikov/ProveIt
Pinned commit: 0ecd158fd163bc4aca0ee40ccf6479ca6cf5f2a8

Inspected paths:

- Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/README.md
- Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/article.tex
- Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceSimplicity.lean

The article ranges inspected were the opening status/abstract, core and
support constructions, binary coding, universe and formalization sections,
and continuation questions. This was not an audit of every assertion in
the repository or every page of the 115-page merged predecessor.

The README marks that merged report unrefereed and not formalized, with its
collection review pending. The actual Lean simplicity theorem inspected
requires an existence hypothesis for a cut separator. It is NOT an
independent arbitrary-small-cut existence theorem.

The repository has not been modified.

## Finite diagnostics

All delivered tests passed:

- 15,018 ordered pairs for labelled common-prefix comparison.
- 2,371 prefix cylinders and 867 proper finite cuts.
- 15,126 finite partial injections.
- 3,868 compressed candidates and 66,873 retained comparisons.
- 16,129 numerical sign-code comparisons.
- 320,000 outer word-code comparisons across two termination conventions.
- 21,844 pair-orientation comparisons.

These diagnostics cover only finite combinatorial kernels. Finite alphabets
have adjacent labels and endpoints, so the crossing test is not a test of
the full saturated-alphabet trichotomy. No experiment verifies singular
cofinality, class comprehension, orbit back-and-forth, or model absoluteness.

## Formal verification

No new Lean theorem was compiled or kernel-checked. The manuscript's module
list and pseudocode are a proposed implementation architecture. A future
formalization must pin its dependencies, establish the actual surreal
small-cut interface, and account for all universe levels.

## Mathematical scope cautions

- The boundary trichotomy uses named prefix cylinders and baseline evaluation.
- The bare-order orbit theorem is a different, coarser classification.
- Equimorphism is not isomorphism.
- A principal normalized cut includes its point on the UPPER side.
- Cardinal support bounds are not ordinal support-location bounds.
- Coverage implies coherence here; the displayed conditions are not claimed
  logically independent.
- The class-extension theorem fixes the set structure and baseline. It is
  not a general absoluteness theorem for arbitrary class existence.
- Raw trace fibers forget tails; singleton fibers can still be non-set-like.
- A coherent injective branch can omit surreal labels.
- A virtual quotient is not a same-sort collection of class equivalence classes.

The written proofs remain unrefereed and merit independent review.
