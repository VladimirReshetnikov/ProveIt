# Sources and provenance

Inspected on 30 September 2026. Repository access used the connected GitHub
plugin. No repository writes were performed.

## Pinned repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Snapshot commit:
`f4457a1d19701d32e8f324240c497653d235b53e`

Path:
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Anchored_Dyadic_Recovery_Uniform_Spectrum/article.tex`

Content blob:
`50cc46f4084386b48378cbc9c1d942c66ce64741`

Canonical pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/f4457a1d19701d32e8f324240c497653d235b53e/Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/inverse-and-sampling/Anchored_Dyadic_Recovery_Uniform_Spectrum/article.tex

Title: *Anchored Recovery of the Dyadic Uniform Spectrum: A sharp
stretched-exponential modulus, lacunary counterexamples to Hölder stability,
and Lipschitz recovery of every fixed prefix*. Dated 29 September 2026.

The exact research target is the third question in its final further-research
section, titled **The sharp separation boundary rho=1/2**. Its stated
hypotheses are a_(j+1) <= a_j/2 with variance 1/9. The source's exact K-class
definition and derivative discussion were also inspected; the new witness
family is checked against those conditions, not against a weaker substitute.

Read ranges included the opening definitions and main statements, lines
300–700, 730–880, 1050–1320, and 1340–1530. The last range contains the
question and the editorial Lean crosswalk. The new manuscript records
crosswalk theorem names as repository-reported provenance, not as an audit
of compiled formal code.

The predecessor is a research manuscript, not a refereed publication. Its
fixed-positive-slack comparison is attributed to it; the new critical
upper and lower proofs do not depend on its unformalized estimates.

## Primary external literature

1. Juan Arias de Reyna, *An infinitely differentiable function with compact
   support: Definition and properties*, arXiv:1702.05442 (2017), English
   translation of the 1982 article in Rev. Real Acad. Ciencias Madrid 76,
   21–38.
   https://arxiv.org/abs/1702.05442
   https://arxiv.org/pdf/1702.05442
   Used for established background on the smooth compactly supported
   dyadic probability density. PDF first page visually inspected.

2. Sara C. Billey and Joshua P. Swanson, *The metric space of limit laws for
   q-hook formulas* (2022), DOI 10.5070/C62257868. Author manuscript
   arXiv:2010.12701, version 2 (2023).
   https://doi.org/10.5070/C62257868
   https://arxiv.org/abs/2010.12701
   https://arxiv.org/pdf/2010.12701
   Used for existing generalized-uniform-sum identifiability and
   parametrization background. PDF first page visually inspected.

3. Wassily Hoeffding, *Probability inequalities for sums of bounded random
   variables*, Journal of the American Statistical Association 58(301)
   (1963), 13–30, DOI 10.1080/01621459.1963.10500830.
   https://doi.org/10.1080/01621459.1963.10500830
   Publisher metadata/search text inspected; direct page access returned
   HTTP 403. The manuscript includes a self-contained proof of the bounded
   concentration inequality it uses.

## Priority caveat

The source review and keyword searches were targeted. Neither repository-wide
absence of every related result nor exhaustive historical novelty is claimed.
The proposed research contribution is precisely mapped to the pinned source's
open boundary question. Standard majorization, convolution, and statistical
tools are not represented as new inventions.
