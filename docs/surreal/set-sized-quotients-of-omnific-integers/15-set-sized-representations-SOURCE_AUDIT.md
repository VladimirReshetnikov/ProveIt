# Source, novelty, and verification audit

Date: 23 September 2026.

## Fixed project snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Commit: `71e9606d297c9b98c732070dc462682cc6948981`

The project was inspected through the connected GitHub tools. No local
clone or Lean build was performed. The source text needed for comparison
was read through the connector; no repository files were modified.

### Material actually inspected

- Root directory metadata and recursive-tree metadata at the snapshot.
- Root `README.md`, including a separately retrieved range of source lines
  420–720. The initial large README response was truncated; this was not
  treated as a complete audit of the file or the implementation.
- `docs/README.md`, including the report inventory and the catalogue entry
  describing universal set-sized quotients of the surreal rotation group.
- The `docs/new` tree, which contained only its procedural README.
- The directory listing of `docs/surreal/euclidean-three-space`.
- The full text of
  `docs/surreal/euclidean-three-space/10-rotation-quotients-SOURCE_AUDIT.md`.
- A repository code search for `omnific`, which returned no matches.
  Index coverage is unknown; this negative result is not a proof that
  no related material exists in the project.

This was a targeted comparison, not a line-by-line reading of every report,
all historical sources, or all Lean modules. The article explicitly credits
the project's analogous rotation-group universal quotient. It does not
claim to have originated the general idea of using a size obstruction to
construct a universal small quotient.

## Primary published / preprint sources used mathematically

1. John H. Conway, *On Numbers and Games* (1976), and Harry Gonshor,
   *An Introduction to the Theory of Surreal Numbers* (1986), are the
   classical references for normal forms and omnific integers. The current
   proof does not claim these constructions as new.

2. Olivier Bournez and Quentin Guilmant,
   *Surreal fields stable under exponential and logarithmic functions*,
   arXiv:2201.08199v1 (2022).
   https://arxiv.org/abs/2201.08199
   https://arxiv.org/html/2201.08199v1
   Sections 2.1–2.3 supply an accessible primary account of cut separation,
   Conway monomials, normal forms, and coefficientwise/convolution arithmetic.

3. Sonia L'Innocente and Vincenzo Mantova,
   *A factorisation theory for generalised power series and omnific integers*,
   Advances in Mathematics 442 (2024), article 109513.
   DOI: https://doi.org/10.1016/j.aim.2024.109513
   Inspected preprint: https://arxiv.org/html/1710.07304v5
   PDF: https://arxiv.org/pdf/1710.07304
   The introduction, Theorem B, and related discussions were inspected.
   Relevant PDF pages for the normal-form definition and Theorem B were
   also inspected as screenshots. Theorem B states exactly that
   omega^(sqrt(2)) + omega + 1 is prime in the full omnific-integer ring.
   The paper already includes geometric divisibility examples and
   monomial-generated-ideal results. None of those facts is claimed new here.
   Published volume/article metadata was checked against the institutional
   repository at https://eprints.whiterose.ac.uk/id/eprint/208281/ .

## Additional searches and scope limitations

Searches included combinations of `omnific integers` with `homomorphism`,
`constant`, `set-sized`, `quotients`, and related ring/representation terms.
Some searches produced irrelevant or very broad results. Those results
were not used as evidence for novelty.

A current search also surfaced `gaearon/conway-refinement`. Its first
100 README source lines were retrieved through GitHub. The repository
presents a claimed Lean proof of the refinement statement. It was not
built or audited here, and it is not a mathematical dependency of this
article. The article deliberately makes no assertion about the current
settlement status of Conway's refinement problem and does not claim a
solution to it.

No identical formulation of the main constant-term universality theorem
was located in the material actually inspected. This is a limited search,
not an exhaustive historical-priority certification.

## Contributions and dependency boundaries

### Candidate contributions of this manuscript

- For every fixed purely infinite element, arbitrarily large families of
  positive-exponent monomials whose pairwise differences divide it with
  positive-support quotients; also a simultaneous set-family version.
- The universal constant-term quotient of the full omnific ring and of
  A + I_K for K = R or C, with arbitrary set-sized associative targets.
- The consequent description of every set-sized module, quotient,
  Gaussian representation, and the associated size-sensitive projectivity
  distinction.
- The explicit application to infinite prime quotients with no nonzero
  set-sized modules, using the published primality input listed above.
- The local cardinality criterion and explicit finite-support extension
  obstruction, with their stated scope.

### Background / straightforward deductions, not independent novelty claims

- Conway normal forms and the omnific constant-term decomposition.
- Hahn convolution and the geometric inverse.
- Finite congruence calculations and the resulting ordinary profinite
  and p-adic inverse systems.
- Standard module, quotient, polynomial, and localization universal
  properties, once the main theorem has been established.
- Gaussian-integer Euclidean arithmetic.
- The published primality theorem for omega^(sqrt(2)) + omega + 1.

## Proof audit checklist

The manuscript explicitly handles the following potential pitfalls:

- A positive support need not have a least exponent. A lower surreal
  bound is obtained by a set cut instead.
- The reciprocal series is checked to remain inside the positive-support
  ideal, not merely inside the ambient field.
- A ring homomorphism is applied only to a finite identity after the
  Hahn quotient has been constructed. No preservation of infinite sums
  is assumed or inferred.
- The collision uses the target's Hartogs ordinal, a set-sized index,
  rather than an informal 'pigeonhole principle for proper classes'.
- Noncommutative target rings are permitted in the main theorem.
- The characteristic-zero quotient kernel is I, not 0*Oz.
- Class quotients use Scott representatives, so proper-class cosets are
  not incorrectly treated as set elements.
- All module-category equivalences are restricted to set-sized modules.
- The finite-support subring and a fixed set-sized Hahn workspace are
  explicitly shown not to satisfy the global conclusion in general.
- The Gaussian statement retains the map of constants and the choice
  of a square root of -1 in the target.
- No classification of all class prime or maximal ideals is asserted.
- Relative-universe targets must be small in the same smaller universe
  that governs supports and cut options.

## Executed finite checks

`verify_identities.py` was executed with exact rational arithmetic and
fixed seed 20260923. The final `finite_checks.json` records 820 passing
cases and no failures:

- 120 explicit finite geometric-divisor truncations;
- 180 generic finite-support divisor truncations;
- 200 constant-term sum/product checks;
- 200 finite-support evaluation-at-one checks;
- 120 Gaussian evaluations into exact 2-by-2 rational matrix rings.

These computations test finite identities only. They do not establish
arbitrary-support well ordering, the infinite Hahn identity, the
Hartogs argument, the prime example's primality, or the quotient coding.
No Lean proof of the new results and no independent referee review have
been performed.

## Artifact quality checks

The article was compiled with LaTeX, its page images were rendered and
visually inspected, and layout/cross-reference corrections were applied.
The final deliverables include only source, PDF, the finite checker and
its report, and the explanatory markdown files; no font files or build
auxiliaries are included in the ZIP.
