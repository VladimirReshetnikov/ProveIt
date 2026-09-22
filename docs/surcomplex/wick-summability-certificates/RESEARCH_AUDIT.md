# Research and novelty audit

Date: September 22, 2026.

## Candidate contribution

The candidate-new object is the joint package consisting of:

1. The exact diagramwise Hahn summability criterion, its finite Hilbert-basis
   description, and its strict valuation-balancing characterization over arbitrary
   nontrivial divisible ordered abelian value groups.
2. Equivalence of all pairable external monomial sectors with the vacuum sector.
3. Equality of the connected and full diagramwise domains for interaction valence
   at least two, with explicit connected amplification of every bad indecomposable
   pattern.
4. The positive-covariance simplification, sharp multiscale stationary-phase
   condition, and mixed-instability and cancellation boundaries.

No novelty is claimed for Wick's pairing formula, the connected-diagram formal
logarithm, ordinary stationary-phase degree counting, Hahn substitution at
infinitesimals, Dickson finiteness, or Fourier–Motzkin elimination.

## Repository snapshot and successful reads

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned main-tree commit:
`4cf691c7d951e037739d32d9f5c387dcce724f3c`

The GitHub connector was used for the following read-only operations:

- Recursive main-tree metadata, yielding the pinned commit.
- Metadata for `docs` at that commit.
- Full `docs/README.md`.
- Recursive tree metadata for `docs/new`, tree
  `9b54f1971086ba7a6e8f1cd711e68a6b3ac4a559`.
- Lines 1–190 of
  `docs/physics/surreal-scalars-and-spacetime/article.tex` at the pinned commit.
- Repository code searches for `Wick` and `Gaussian`; both returned no matches.

The README catalogs 26 reports. The full catalog was read to avoid repeating its
obvious analysis, dynamics, spectral, polynomial, and physics directions. The
physics source excerpt was used only for its declared scope, not as evidence about
unseen portions of that article.

## Compressed archives: titles inspected, interiors not fully inspected

The `docs/new` tree listed these 18 archives:

```
hahn_tate_uniformization.zip
surcomplex_exact_and_drifting_multipliers.zip
surcomplex_exact_jet_image.zip
surcomplex_hahn_hilbert_spectral_theory.zip
surcomplex_infinite_spectral.zip
surcomplex_interpolation_research.zip
surcomplex_regular_singular.zip
surcomplex_single_loss_article.zip
surcomplex_tate_uniformization.zip
surreal_autonomous_dynamics.zip
surreal_exponential_automorphism_rigidity.zip
surreal_exponential_rigidity.zip
surreal_holonomic_rigidity(1).zip
surreal_holonomic_rigidity.zip
surreal_localization_bundles.zip
surreal_symbolic_dynamics.zip
surreal_tail_span_research.zip
surreal_theta_research.zip
```

A request to fetch the binary theta ZIP through the GitHub connector was rejected
because that action supports UTF-8 text. A container clone failed to resolve the
configured proxy, and attempted raw/archive downloads did not succeed. There was
no successful full checkout, archive extraction, or repository-wide textual scan.

Therefore **no claim is made that every repository file or ZIP interior was
inspected**. Search absence and filenames are not evidence that an equivalent
result is absent from an archive.

## Primary literature compared

### Hahn and surreal foundations

B. H. Neumann, *On ordered division rings*, Transactions AMS 66 (1949), 202–252.
DOI: https://doi.org/10.1090/S0002-9947-1949-0032593-5

The positive-support lemma is imported as classical. The article does not claim
to reprove its most general ordered-series form.

A. Berarducci and V. Mantova, *Surreal numbers, derivations and transseries*, JEMS
20 (2018), 339–390. DOI: https://doi.org/10.4171/JEMS/769
Preprint: https://arxiv.org/abs/1503.00315

The normal-form and summability portions of the text, especially Sections
2.3–2.6, were inspected. The paper's differential-algebra results are not used as
premises of the new Wick criterion.

### Classical Gaussian and connected-diagram calculus

P. Etingof, *Mathematical Ideas and Notions of Quantum Field Theory*, Graduate
Studies in Mathematics 254, AMS, 2026.
Author-hosted 405-page preliminary version:
https://math.mit.edu/~etingof/gsm254.pdf
Related arXiv version: https://arxiv.org/abs/2409.03117v2

The weighted Feynman theorem and connected-diagram identity in Chapter 3 were
inspected, including their formal-parameter interpretation. The author-hosted
book was followed from the arXiv page so that comparison was not confined to the
shorter notes. Text and selected page images were inspected. These sources are
not included in the ZIP because they are third-party works.

### Related boundaries

M. Joswig and B. Smith, *Convergent Hahn series and tropical geometry of higher
rank*, JLMS 107(4) (2023), 1450–1481.
https://doi.org/10.1112/jlms.12716
https://arxiv.org/abs/1809.01457

Publication metadata and abstract were checked. No exhaustive full-text
comparison is claimed, and no theorem from this paper is used as an unproved
premise of the present results.

D. Sauzin, *Introduction to 1-summability and resurgence*, 2014.
https://arxiv.org/abs/1405.0356

This is cited for the distinction between Borel–Laplace summation and strong
Hahn summability, not for an asserted identification of the two procedures.

## Search scope and conclusion

Targeted searches combined phrases involving Hahn series, Wick expansions,
Gaussian perturbation, valuation balancing, ordered groups, and Hilbert-basis
certificates. Several returned results were weakly relevant; they do not provide
a reliable proof of absence. The precise theorem package was not located in
successfully inspected materials.

The novelty conclusion is **provisional**. An expert literature/priority review
and an audit of the currently unread repository archives remain necessary before
claiming that no equivalent result has appeared anywhere. This limitation is
stated on the title page and in Section 13 of the article rather than hidden in
this auxiliary file.
