# Sources and provenance

## Repository snapshot

Repository: VladimirReshetnikov/ProveIt

Commit consulted: `0c973d8f5e7ef4550f4df1bf486d890037fd9f14`.

Root of the relevant documentation:
https://github.com/VladimirReshetnikov/ProveIt/tree/0c973d8f5e7ef4550f4df1bf486d890037fd9f14/Analysis/Transseries/docs/series-and-transseries

The following were read through the GitHub connector at that pinned snapshot:

- `Analysis/Transseries/docs/series-and-transseries/README.md`: current structure,
  nineteen unmerged research arrivals, and the distinction between prose
  research results and the scope of existing Lean formalization.
- `Exponential_Feedback_Regularity_Classification/README.md` and `article.tex`
  beneath that root: the feedback model, coefficient regularity, left-sector
  construction, and the explicit absence of uniform Gevrey remainders and a
  directional Borel-summation theorem. This is the specific research gap pursued.
- `Finite_Core_Universality_Exponential_Feedback/README.md`: neighboring
  coefficient/saddle/inverse work, consulted for scope and non-duplication.

The much larger canonical volume was located, but oversized-content retrieval
was not used as evidence for a claim-by-claim audit. The final article does not
claim an exhaustive audit of the entire repository. It proves its central
coefficient estimates independently and does not depend on unreviewed exact
numerical-type or saddle-equivalent claims from neighboring drafts.

## Primary literature

Nikita Nikolaev. *Gevrey asymptotic implicit function theorem*.
L'Enseignement Mathematique 70 (2024), 1/2, 251-282.
DOI: 10.4171/LEM/1061. Preprint: arXiv:2112.08792.
https://doi.org/10.4171/LEM/1061
https://arxiv.org/abs/2112.08792

Alberto Lastra, Stephane Malek, Javier Sanz.
*Summability in general Carleman ultraholomorphic classes*.
Journal of Mathematical Analysis and Applications 430 (2015), 2, 1175-1206.
DOI: 10.1016/j.jmaa.2015.05.046. Preprint: arXiv:1402.1669.
https://doi.org/10.1016/j.jmaa.2015.05.046
https://arxiv.org/abs/1402.1669
https://arxiv.org/html/1402.1669
Relevant primary-text locations: Example 2.2, Definition 3.3, Theorem 3.18,
and Remark 3.19(i). The HTML primary text was used to check the summability
characterization and its relation to ordinary k-summability.

Javier Sanz. *Flat functions in Carleman ultraholomorphic classes via proximate
orders*. Journal of Mathematical Analysis and Applications 415 (2014), 2,
623-643. DOI: 10.1016/j.jmaa.2014.01.083. Preprint: arXiv:1402.2627.
https://doi.org/10.1016/j.jmaa.2014.01.083
https://arxiv.org/abs/1402.2627

Alan D. Sokal. *An improvement of Watson's theorem on Borel summability*.
Journal of Mathematical Physics 21 (1980), 2, 261-263.
DOI: 10.1063/1.524408.
https://doi.org/10.1063/1.524408
This is cited as a possible route for the unresolved boundary-domain problem;
its hypotheses are not asserted to have been established for quadratic feedback.

## Attribution boundary

The article's bibliography is embedded in its TeX source. General implicit
function and summability methods are classical. The application to this
countable feedback kernel, including the explicit coefficient-to-remainder
bridge and the k > 1 iff criterion, is presented as a proposed contribution,
not as an independently certified publication-priority claim.
