# Source provenance and scope of inspection

Manuscript date: 6 October 2026.

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit used for the principal comparisons:
`5ea1d06dd2f2d3a30e96016b236e3f1e3dfb048f`.

The GitHub connector was used to read repository resources. No write action was
performed. This was a focused inspection, not a full repository audit, clone,
or compilation.

Relevant inspected resources:

1. `Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections06_07.lean`
   - Blob: `57b79242466ca9ddf5c36c76b828d7c5557f58ca`.
   - The inspected section includes Lemma 7.5 with explicit prime-modulus
     hypothesis and size bound `|B|/(8k C^(4k))`.
   - Also includes the original Corollary 7.6 constants.

2. `Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections08_09.lean`
   - Blob: `0fb6e0a1de3f046f436747603f7eeb06f8d1f074`.
   - The complete short statement file was read.
   - Lemma 9.3 is stated without a primality assumption, with a size threshold,
     coefficient `(alpha eta/4)^(2^19)`, and approximate order-eight respect.
   - Corollary 9.4 includes the auxiliary `gamma^7 beta^6` factor.

3. `Combinatorics/Ramsey/Lean/GowersSzemeredi/Proofs09Restriction.lean`
   - Blob: `29bb4178fbec83d177200ce2c2978a3c0b245112`.
   - Its introductory definitions and the search result for
     `lemma_9_3_holds` were inspected.
   - The existence of that theorem in source is not a claim that this delivery
     independently compiled or kernel-checked the module.

4. `Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md`
   - Inspected for nearby results, overlap, status, and stronger prime-field
     constants. Some returned responses were long and excerpts were read.
   - The guide records existing prime-field bounds stronger than the universal
     size guarantee in this article. No result from that guide is needed as an
     unproved premise of the present proofs.

5. `24-section7-compression-PROVENANCE.md` in the preceding research directory.
   - Read to identify primary references and existing BSG comparisons.
   - It is provenance material, not an input theorem.

6. `Definitions.lean` was additionally queried for tuple, graph, and approximate
   homomorphism conventions. The source response was large; no claim of a
   complete audit of that file is made. A later live search returned a newer
   commit; it did not replace the pinned baseline above.

## Primary mathematical references

- W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001), 465–588.
  DOI: https://doi.org/10.1007/s00039-001-0332-9
  PDF: https://www.cs.umd.edu/users/gasarch/TOPICS/vdw/sz-thm-gowers-proof.pdf
  Relevant original pages were visually inspected, including printed
  503, 505–506, and 516. The order-eight comparison uses the original
  `(alpha eta/4)^(2^19)` coefficient.

- Giorgis Petridis, *New Proofs of Plünnecke-type Estimates for Product Sets in
  Groups*, Combinatorica 32 (2012), 721–733; arXiv:1101.3507.
  https://arxiv.org/abs/1101.3507
  https://arxiv.org/html/1101.3507v3
  The minimal-growth method is standard and explicitly attributed. The article
  includes its own exposition and derivation of the required inequalities.

- Jacob Fox and Benny Sudakov, *Dependent Random Choice*, arXiv:0909.3271.
  https://arxiv.org/abs/0909.3271
  Background attribution for the common-neighborhood method. The numerical
  BSG estimate used in the manuscript is proved in full there.

- Ben Green and Imre Z. Ruzsa, *Freiman's theorem in an arbitrary abelian group*.
  DOI: https://doi.org/10.1112/jlms/jdl021
  https://arxiv.org/abs/math/0505198
  Context for the future structural-defect question; not a dependency of the
  main restriction or obstruction proofs.

## Priority and content boundaries

The source comparison is targeted, not exhaustive. The exact formulations and
constant combinations in this manuscript are offered for evaluation, but
publication priority has not been independently established. Broad searches
also returned irrelevant pages; those pages were not used as mathematical
sources.

The ordinary BSG principle, Plünnecke–Ruzsa estimates, character duality,
finite averaging, and Fourier norm inequalities are not claimed as new.

This package does not contain copies of Gowers's paper, other cited papers, or
repository source modules. It contains the new exposition, explicit derivations,
reference implementation, and results of the finite checks.
