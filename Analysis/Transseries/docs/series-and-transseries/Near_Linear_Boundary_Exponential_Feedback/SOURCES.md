# Sources and provenance

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Initial survey root **tree** SHA (not a commit SHA):
`a795fcffa4b3ece22761d81fbed3c43be8b81795`

Initial `Analysis/Transseries` project tree SHA:
`e37727630fd519201ceb2b2f24fdc71b238873d9`

The direct predecessor was checked unchanged at commit:
`04473354a0f3edff2d6c365caf26170ca6b88735`

Direct predecessor:
`Analysis/Transseries/docs/series-and-transseries/Exponential_Feedback_Regularity_Classification/article.tex`

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/04473354a0f3edff2d6c365caf26170ca6b88735/Analysis/Transseries/docs/series-and-transseries/Exponential_Feedback_Regularity_Classification/article.tex

Blob SHA:
`c6a83d71973a12fe7ed970d2abc56e2b49e6808f`

Title: *A Sharp Regularity Classification for Countable Exponential-Feedback Transseries*.

Relevant contiguous source ranges inspected: lines 350–530 (Lagrange coefficient formula, positivity, convergence), 1400–1605 (further research and status); lines 1450–1490 were rechecked at the final commit. The named near-linear question begins at line 1455 of that snapshot. It asks for sharp coefficient asymptotics and natural summation scales for `j(log j)^beta` and `jL(j)` with slowly varying unbounded L. The amplitude question follows it.

The project and series-group READMEs were also inspected. The group README initially listed six arrivals, then twelve after the second September 29 intake. The additional intake descriptions were checked at final review. This was not a line-by-line audit of the entire canonical volume, companion volume, or every repository file. The group README describes the incoming papers as not yet reviewed claim by claim and not formalized in Lean. The finite formula needed for this article is reproved rather than used as a trusted formal dependency.

## Primary external references

1. Ira M. Gessel, *Lagrange Inversion*, Journal of Combinatorial Theory, Series A 144 (2016), 212–249. https://arxiv.org/abs/1609.05988 ; https://doi.org/10.1016/j.jcta.2016.06.018
2. Sabine Jansen, Tobias Kuna, Dimitrios Tsagkarogiannis, *Lagrange inversion and combinatorial species with uncountable color palette*, Annales Henri Poincaré (2021). https://arxiv.org/abs/2008.10862 ; https://doi.org/10.1007/s00023-020-01013-0
3. N. H. Bingham, C. M. Goldie, J. L. Teugels, *Regular Variation*, Encyclopedia of Mathematics and its Applications 27, Cambridge University Press, 1987. Background attribution; all differentiable estimates used in the proof are proved in the article.
4. David Sauzin, *Introduction to 1-summability and resurgence*, 2014. https://arxiv.org/abs/1405.0356
5. Nikita Nikolaev, *Gevrey Asymptotic Implicit Function Theorem*, 2021, version 2. https://arxiv.org/abs/2112.08792
6. NIST Digital Library of Mathematical Functions, Section 4.13, Lambert W-function. https://dlmf.nist.gov/4.13

The external references supply classical tools and context, not the specific borderline theorem claimed in this article. Searches and source checks did not constitute an exhaustive publication-priority review. No assertion of global priority or a previously unknown classical inversion formula is intended.

## New proof boundaries

- The sharp root law and LDP are proved for the explicit positive, smooth, convex profile class, with exponential amplitude control and bounded linear slope perturbations.
- The Borel transfer is proved by maximum-term estimates; it is not imported from a general Gevrey implicit-function theorem.
- The scalar reversion coefficients are classical. Their application to the feedback Borel normalizer, the retained resonance constants, and the uniform transition are derived in the article.
- The work does not claim multiplicative coefficient equivalents, a central limit theorem, condensation, summability off the positive ray, or a compatible acceleration.
