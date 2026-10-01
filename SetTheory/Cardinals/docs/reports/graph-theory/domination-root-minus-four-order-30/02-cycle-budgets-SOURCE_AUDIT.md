# Source, dependency, and claim audit

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: `0744012ba29db0e345c44be953c6de3e000439e6`.

Main directory:
`SetTheory/Cardinals/docs/reports/graph-theory/domination-root-minus-four-order-30/`

Inspected target files: `README.md`, `domination_root_30.tex`, and
`code/search.py`. The repository research index and several other report
READMEs were inspected when selecting the topic, but no exhaustive audit
of every repository theorem is claimed.

The source report already supplies the exact 30-vertex root -4 example,
its simplicity, cycle rank two, and the zero-C rooted-tree search.
It also already records that two is the minimum cycle rank for root -4,
using Oboudi's trees/unicyclic exclusion. These are not claimed as new.
The exact edge list in `check_repo_example.py` is transcribed with attribution
from equation (2.1) of that report.

## External primary sources

1. S. Alikhani and M. Griswold, *On the Integer Domination Root Conjecture*,
   arXiv:2608.00109v1 (2026), https://arxiv.org/html/2608.00109v1.
   The HTML article was inspected. It states the earlier 33-vertex root -4
   construction and the further-root questions.
2. S. Alikhani, *The Domination Polynomial of a Graph at -1*, Graphs and
   Combinatorics 29 (2013), 1175-1181,
   https://doi.org/10.1007/s00373-012-1211-x.
   The publisher abstract and bibliography were inspected. Full subscription
   text was not available through the inspected page. Connected realizability
   of every odd value is in the abstract. Oddness is attributed to Brouwer in
   the bibliography and is reproved self-containedly in the new article.
3. T. Kotek, J. Preen, F. Simon, P. Tittmann, and M. Trinks,
   *Recurrence Relations and Splitting Formulas for the Domination Polynomial*,
   Electronic Journal of Combinatorics 19(3) (2012), P47,
   https://www.combinatorics.org/ojs/index.php/eljc/article/view/v19i3p47.
   The publisher page was inspected. General recurrence/splitting methods
   are credited; no unseen theorem is used as a premise.
4. S. Alikhani and Y.-H. Peng, *Introduction to Domination Polynomial of a Graph*,
   Ars Combinatoria 114 (2014), 257-266; https://arxiv.org/abs/0905.2251.
   Standard definitions/background, also proved directly when used.
5. M. R. Oboudi, *On the roots of domination polynomial of graphs*, Discrete
   Applied Mathematics 205 (2016), 126-131,
   https://doi.org/10.1016/j.dam.2015.12.010.
   The direct DOI fetch was blocked. The trees/unicyclic statement is credited
   as cited in the inspected repository report and Alikhani--Griswold article.
   It is contextual only; none of the new structural proofs depends on it.

Access date: 30 September 2026. Targeted searches did not establish priority
for the new claims. They are not a systematic literature review, and we do
not assert that every lemma or the sharp inequality is absent from all
prior work.

## Claim boundaries

Conventional proofs: constrained-forest cancellation; sharp 3^beta bound;
simultaneous root budget; four ordinary tree signatures; exact tree pruning;
four-subdivision invariance; complete bicyclic spectrum; zero-C search
obstruction; arithmetic corollaries based on those theorems.

Computer-assisted: the exact tricyclic kernel image table and consequences
that use it. The completeness reduction is proved in the article, and the
finite arithmetic table is exhaustively checked by supplied code.

No Lean code was generated or tested. No claim of peer review, global
publication priority, a graph with root -6/-8, global minimum vertex order,
or sufficiency of the divisibility test is made.

The exploratory failed gadget searches were used only to guide the research.
No theorem relies on their search limits or on absence of a discovered hit.
The delivery contains the final proof/certificate system, not those large
experimental catalogues.
