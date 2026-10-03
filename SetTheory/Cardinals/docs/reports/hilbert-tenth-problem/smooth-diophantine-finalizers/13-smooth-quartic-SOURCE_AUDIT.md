# Source and provenance audit

Date: 2 October 2026.

## Repository review

Repository: https://github.com/VladimirReshetnikov/ProveIt

Read through the GitHub connector:

- `README.md`, on the live default branch. The returned blob was
  `bc4c514b61e30106f0a914272cbc87b5449f1151`.
- `Computability/HilbertTenthProblem/README.md`, live branch, for the current
  distinction between complete/universal compilers and bounded substrate reports.
- `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/README.md`,
  for the scope and provenance of the existing witness-faithful reports.
- `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/01-causal-traces-RESEARCH_STATUS.md`,
  pinned at commit `a845ab5d0f4591294ef3c2d92feaeb5825a8d543`.
  Its returned Git blob was `e768b2284c6723d21d77edfb24f786ccdb83585a`.

The overview reads were not all frozen to one snapshot. The paper records this
explicitly. Targeted searches for Foata/canonical certificates and smooth
Diophantine topics helped avoid duplicating the existing frontend catalogue.
No absence-of-prior-work conclusion is inferred from the search results.
No files were changed in the repository. No repository build was run.

## Primary external sources

1. Bjorn Poonen, *Automorphisms mapping a point into a subvariety*, with an
   appendix by Matthias Aschenbrenner, Journal of Algebraic Geometry 20 (2011),
   785–794. Author manuscript dated 14 July 2009:
   https://math.mit.edu/~poonen/papers/automorphism.pdf
   The five-page author manuscript was read; the page containing Lemma 4.1 was
   also inspected as an image. Relevant points: known smoothness reduction,
   smooth-projective-closure undecidability, and the four-square domain bridge.
   The manuscript does not supply the five-variable weighted formula used here.
   That observation is not an exhaustive publication-priority claim.

2. Dominique Larchey-Wendling and Yannick Forster, *Hilbert's Tenth Problem in
   Coq (Extended Version)*, LMCS 18(1):35 (2022), arXiv:2003.04604v5:
   https://arxiv.org/abs/2003.04604
   The primary record establishes the scope of the mechanized MRDP background
   and the Minsky-machine/FRACTRAN route. No new Coq development is claimed here.

3. The Stacks Project, Tag 01V4, *Smooth morphisms*:
   https://stacks.math.columbia.edu/tag/01V4
   Used for the standard-smooth/hypersurface Jacobian criterion. The integral
   unit identity itself is derived explicitly in the paper.

## New derivations and trust boundary

The paper develops the weighted finalizer, its lattice bijections, its universal
Jacobian identity, the dyadic construction using weights (1,1,2,2), rational
and real-geometric consequences, and a restricted minimality obstruction.
Ordinary mathematical proofs, not external source assertions, support these.

The Python compiler and tests were authored for this package. Test reports are
actual execution outputs. The proofs of general smoothness, integrality,
density, universal computation, and restricted minimality are not represented
as consequences of finite testing alone.

A full literature review of smooth integral models with prescribed arithmetic
fibres remains a proposed research task. The package does not certify that any
result is historically first.
