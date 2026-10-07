# Source scope and numerical provenance

This note accompanies Report 227, dated 5 October 2026. The article contains the mathematical proofs and its full bibliography. This file records the scope of the source comparison and the status of reproducibility data.

## The OEIS definitions

- https://oeis.org/A244407 defines the even half-size diagonal T(2n,n), starting at n=1
- https://oeis.org/A244410 defines the odd diagonal T(2n+1,n), with the exceptional term a(0)=1
- https://oeis.org/A244372 defines the maximum-outdegree-exactly-k triangle for rooted unlabeled trees

The leading constants 0.9495793... and 2.806733... are recorded in the first two entries with attribution to Vaclav Kotesovec, 11 July 2014. They are not labeled explicitly as conjectures. The report proves exact identities and evaluates the resulting constants, rather than claiming those recorded leading equivalents were first proposed here.

The data files distinguish exact-generated regression fixtures from separately identified samples of the displayed OEIS entry. Exact-generated fixtures are mathematical computations, not a downloaded OEIS b-file. No b-file comparison is claimed. Entries were consulted on 5 October 2026; downloaded third-party papers are not redistributed in this archive.

## Classical work used

Schwenk (1977), DOI 10.1016/0012-365X(77)90008-5, gives the classical cycle-index asymptotics. Its constant is cross-checked against the clean expression in equation (2.10) of Drmota and Gittenberger (1999), author manuscript https://dmg.tuwien.ac.at/bgitten/preprints/nodedeg.pdf. Their local coefficient b multiplies sqrt(rho-z), whereas this report's beta multiplies sqrt(1-z/rho), so beta=b sqrt(rho). Historical printed decimals are not high-precision certificates.

Gittenberger (2006), https://www.dmg.tuwien.ac.at/bgitten/preprints/largedeg.pdf, treats growing-degree normal, Poisson and degenerate regimes. Its uniform O(1) absolute mean error cannot be used as a relative bound for an exponentially small event. Report 227 proves its relative count estimate by ordered-pair orbit objects instead.

The Pólya–Otter square-root singularity, full finite jets and transfer calculus are classical. Genitrini (2016), https://arxiv.org/abs/1605.00837, develops full asymptotic expansions for Pólya structures; Flajolet and Sedgewick's Analytic Combinatorics supplies the general analytic framework. Lambert-W inversion and the branch distinction are classical, as in Corless et al. (1996), DOI 10.1007/BF02124750. These methods are credited, not presented as new general methods.

The 2026 Bassan–Donderwinkel–Kolesnik forest paper, DOI 10.1007/s10959-026-01513-5, concerns component counts in a different large-forest model. Its integer-moment convergence is not imported into the excess decoration here, whose limiting positive-integer moments are infinite.

## Unresolved full-text priority comparison

Goh and Schmutz, Unlabeled trees: Distribution of the maximum degree, Random Structures & Algorithms 5 (1994), 411–440, DOI https://doi.org/10.1002/rsa.3240050304, remains a necessary full-text comparison. The author-hosted PDF https://www.math.drexel.edu/~eschmutz/PAPERS/ult2.pdf was unavailable through the attempted public routes. Publisher restrictions were not bypassed.

The publisher record and indexed primary fragments indicate a principal logarithmic central-window theorem. Bartholdi and Diaconis (2026), DOI https://doi.org/10.1017/fms.2026.10218, reproduce that theorem with attribution. Neither abstract, fragments nor the later citation can exclude an overlapping rare-tail lemma elsewhere in the original paper. The comparison is therefore incomplete. The report makes no worldwide novelty or first-discovery claim.

## What is proved and what is computed

- Exact formulas and asymptotic statements have proofs in the article
- Finite enumeration and coefficient comparisons check implementation and normalization; they do not prove an infinite range
- All orders means every fixed finite truncation, with its stated remainder; it does not mean a convergent infinite series
- The exact two-sector decomposition retains an exponentially small defect. A fixed algebraic approximation to the principal sector need not resolve that defect numerically
- Floating-point constants, finite-sum critical evaluations, coefficient jets, ratios and inverse diagnostics are not interval-certified enclosures
- The inverse theorem gives asymptotic two-ceiling bounds. No effective enclosure constant or finite starting threshold is certified
