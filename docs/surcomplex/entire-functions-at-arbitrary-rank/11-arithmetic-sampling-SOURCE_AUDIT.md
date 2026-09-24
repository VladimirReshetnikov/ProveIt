# Source, novelty, and proof audit

Date: 23 September 2026.
Manuscript: **Arithmetic Sampling in Surreal Hahn Fields**.

## Repository snapshot and retrieval

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned tree:

```text
343dc2c471212bb9b53ff4623bace2e1943f255b
```

The repository was accessed with the connected GitHub reader. Tree and
contents metadata established the snapshot and report locations. A local
clone was attempted but failed because network name resolution was
unavailable; no local repository build followed.

Targeted source reads included:

1. `README.md`, initial portion (requested lines 1–220).
2. `docs/README.md`, the report inventory and scope descriptions.
3. `docs/surcomplex/entire-functions-at-arbitrary-rank/README.md`, initial
   portion (requested lines 1–250).
4. `docs/surcomplex/entire-functions-at-arbitrary-rank/article.tex`, a
   passage beginning at line 330, containing the cofinality, interpolation,
   and scalar-extension statements and their surrounding scope notes.
5. `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`, initial
   portion (requested lines 1–130), including its source inventory.
6. `docs/surreal/omnific-preserving-automorphisms/README.md`, the later
   question and source-comparison portion (requested lines 400–720).
7. `docs/surreal/omnific-preserving-automorphisms/12-automatic-strongness-SOURCE_AUDIT.md`.
8. `docs/surreal/omnific-preserving-automorphisms/13-omnific-isomorphisms-SOURCE_AUDIT.md`.

Several long connector responses were truncated. Requested ranges are not
represented here as proof that all their contents were returned. The scope
comparison uses the content that was actually visible, supplemented by the
full returned companion audits. The complete entire-function article,
all predecessor manuscripts, and the formalization ledger were not audited.

The omnific-Diophantine report is credited through its descriptions in the
root/documentation guides. Its full article was not read for this work.
The new polynomial constant-term arguments are proved directly in the
manuscript and do not depend on an unaudited theorem from that report.

The later companion audits already propose real omnific automatic-strongness
results. Hence an older merged guide still calling that question open was
not treated as evidence of an unresolved question to solve again.

## Primary external sources

1. Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for
   generalised power series and omnific integers*, arXiv:1710.07304v5.
   https://arxiv.org/html/1710.07304v5
   Used for Hahn/omnific arithmetic background and especially Proposition
   2.4.5, which prevents an unjustified blanket assertion that the fraction
   field of a set-sized canonical integer part is the whole Hahn field.

2. Salma Kuhlmann and Michele Serra, *The automorphism group of a valued
   field of generalised formal power series*, arXiv:2107.03362v3.
   https://arxiv.org/html/2107.03362v3
   Used for standard strong summability definitions and closure properties
   in Section 4. The paper's automorphism decomposition is not an input to
   any proposed new theorem here.

3. The Stacks Project, Section 10.31, *Noetherian rings*, Tag 00FM,
   especially Lemma 10.31.1.
   https://stacks.math.columbia.edu/tag/00FM
   Used for the Hilbert basis theorem and its Noetherian consequences.

4. The Stacks Project, Section 10.39, *Flat modules and flat ring maps*,
   Tag 00H9, especially Lemmas 10.39.11 and 10.39.15.
   https://stacks.math.columbia.edu/tag/00H9
   Used for the equational flatness and faithful-flatness criteria.

5. Natalia Garcia-Fritz and Hector Pasten, *Uniform positive existential
   interpretation of the integers in rings of entire functions of positive
   characteristic*, arXiv:1411.7109.
   https://arxiv.org/abs/1411.7109
   Its abstract was returned by search and used only to recognize existing
   undecidability results for entire-function rings. A subsequent direct
   page open failed. No detailed theorem or proof from this paper is
   imported into the argument.

6. The user-supplied Wikipedia article:
   https://en.wikipedia.org/wiki/Surreal_number
   Orientation only, not the source of a technical theorem or a priority
   claim.

These sources were consulted on 23 September 2026. Searches combining Hahn
fields, entire functions, integer-valued functions, omnific integers, and
non-Archimedean arithmetic often returned irrelevant results. Their failure
to locate an exact antecedent is not evidence of historical originality.

## Established ingredients, not claimed as new

- Hahn normal forms and the canonical omnific support cut.
- Strong summability, support closure, and regrouping rules.
- The entire coefficient criterion and the cofinality obstruction, already
  present in the repository's arbitrary-rank entire report.
- Hilbert's basis theorem, module Gröbner bases, polynomial division, and
  the equational criterion of flatness.
- Ordinary integer-valued polynomial and finite-difference mechanisms.
- Constant-term pullback arithmetic already developed in the repository.
- The classical halting obstruction and the basic infinite-product example.
- The fact that unrestricted full-class strong entireness forces an ordinary
  set-indexed power series to be polynomial.

## Proposed contributions

1. Uniform bounded-degree transfer from scale polynomials back to entire
   Hahn series, with arbitrary valuation rank allowed.
2. Coefficientwise lifting for polynomial matrices over the ordinary
   coefficient polynomial ring; faithful flatness; exact entire normal forms
   modulo ideals defined over that field.
3. Dense ordinary arithmetic sampling, including invertible affine Hahn
   images of such grids, and an exact restriction theorem on algebraic loci.
4. Exact classification of entire canonical-integer-part-preserving maps.
   The novel step proposed here is the analytic collapse to polynomiality;
   the subsequent polynomial arithmetic is credited as established.
5. The finite positive-tail ideal, a sharp actual-scale bound in one
   variable, and the same finite-scale certificate for every finite jet order.
6. Realization of every nonzero polynomial ideal by a nonpolynomial entire
   series precisely in the value-group regime that permits such series.
7. An explicit quadratic-growth computable family with ordinary exceptional
   locus `{0}` or `{0,1}` according to halting, giving a precise limit on
   complete finite-certificate extraction.

These are written-proof claims, not an independent priority determination.
No named published conjecture is claimed settled, and the article does not
claim a new negative solution to Hilbert's tenth problem.

## Critical mathematical checks

- Necessity of the growth criterion uses a descending sequence at a
  shifted monomial point, not a rank-one convergence argument.
- Affine substitution is expanded as a whole family before regrouping.
- Module lifts have one degree-loss constant depending only on the fixed
  polynomial matrix; without this, reconstruction need not be entire.
- The flatness theorem has base `k[X]`, not arbitrary Hahn-coefficient
  polynomial matrices.
- The positive tail tests every exponent, not only the leading valuation.
- The scale-zero polynomial is distinct from the constant power coefficient.
- The `A`-valued locus includes a residue-arithmetic condition and need not
  itself be Zariski closed.
- Actual-scale sharpness does not prohibit shorter certificates made from
  arbitrary polynomial combinations of those scales.
- Finite jet orders use Hasse derivatives; the residue condition is not lost.
- The arbitrary-ideal realization checks all valuation weights, not only
  growth at ordinary points, and assumes countable cofinality exactly where
  nonpolynomiality requires it.
- The machine-family added scales are nonsquares and cannot cancel base
  scales. Every ordinary power coefficient is computable by bounded
  simulation. The quadratic modulus is uniform in the machine.
- The claim of Pi-0-1 completeness concerns the explicit total family indexed
  by machines, so there is no hidden validity test for arbitrary series codes.
- Class-sized surreal conclusions use only set-indexed coefficient families.
- Neither `Frac(A)=K` for an arbitrary set-sized workspace nor a choice-free
  identification of coefficient fields/monomial sections is assumed.

## Verification and build

`verify.py` passes **8,774 exact assertions in ten groups**, using Python
3.13.5 and SymPy 1.14.0, with seed 20260923. The full category counts are in
`verification.json`. These finite checks do not prove infinite or
proper-class statements, flatness, or undecidability. The written proofs
are the evidence for those statements.

There is no Lean or other proof-assistant certificate for this manuscript,
no independent referee report, and no claim that a repository proof build
was run. PDF build and rendering details, plus exact artifact hashes, are
recorded in `build_report.json` and `ARTIFACT_MANIFEST.json`.
