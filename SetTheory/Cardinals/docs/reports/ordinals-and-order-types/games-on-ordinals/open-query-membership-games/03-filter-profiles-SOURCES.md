# Source audit and claim boundaries

Inspected September 29, 2026 (America/Los_Angeles).

## 1. The selected repository question

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned revision: `2d49198382cc068f46747d1b3d9067d47cee4f24`

Selected article:

```
SetTheory/Cardinals/docs/reports/ordinals-and-order-types/games-on-ordinals/open-query-membership-games/article.tex
```

Article blob: `75f0c4d7ba520326e6adf029163f672d1f764192`

The associated README and relevant article sections were retrieved through
the GitHub connector at this revision. Part II, Section 27, Research
question 1 asks for local conditions that make the finite-output
Cantor–Bendixson layer bound sharp and for a characterization by accumulating
word profiles. Its note distinguishes the already-treated binary case from
three or more labels. The source's finite-output article is itself an
AI-assisted, unrefereed report, not a Lean or Rocq development.

The present report resolves the profile and layer-attainment problems for
all Hausdorff spaces with finite nonempty first derived set. It does not
claim to resolve every higher-height instance of the selected question.
It also does not claim to solve Research question 2's general minimum
synchronization-family problem: our ultrafilter thresholds count local
components while permitting all labels to occur at finite isolated
exceptions, a specific input model.

The repository's ordered-layer normal form is reproduced with a full proof.
Its tower formula and binary comparison supply context, not an unverified
logical premise for the new filter theorems.

## 2. Primary literature consulted

1. Lucas Chiozini, Tamás Csernák and Lajos Soukup, *Cut-and-choose games in
   topological spaces*, arXiv:2510.05754v3, revised May 29, 2026.
   https://arxiv.org/abs/2510.05754
   Role: the broader published-preprint game setting. The abstract and
   version history were verified. No theorem about arbitrary transfinite
   play from this paper is imported into the new proofs.

2. Aurélie Lagoutte and Sébastien Tavenas, *The complexity of Shortest
   Common Supersequence for inputs with no identical consecutive letters*,
   arXiv:1309.0422, 2013.
   https://arxiv.org/abs/1309.0422
   Role: background for the repository's word-based complexity setting.
   It is not the hardness input used in our graph-profile reduction.

3. Saeed Akbari, Amir Hossein Ghodrati, Afrouz Jabalameli and Morteza
   Saghafian, *Chromatic Number and Dichromatic Polynomial of Digraphs*,
   arXiv:1711.06293, 2017.
   https://arxiv.org/abs/1711.06293
   Role: an established directed acyclic-set degree bound. The weaker
   one-sided random-order inequality used here is proved in full.

4. Shamil Asgarli, Donald Falkenhagen and Kaya Hoshi, *Improved lower bounds
   for the maximum order of an induced acyclic subgraph*,
   arXiv:2511.02819v3, revised May 6, 2026.
   https://arxiv.org/abs/2511.02819
   Role: primary context for refinements of directed degree bounds. The
   v1 HTML was consulted for background; the current v3 abstract and
   version history were checked during final bibliography review.
   No improved bound from this paper is required by our argument.

5. Alexander Göke, Dániel Marx and Matthias Mnich, *Parameterized Algorithms
   for Generalizations of Directed Feedback Vertex Set*,
   arXiv:2003.02483, 2020.
   https://arxiv.org/abs/2003.02483
   Role: established directed-FVS NP-completeness and parameterized
   algorithm context. The NP-completeness assertion is the only imported
   complexity-theoretic fact in our hardness claims. The reductions to
   layer count and rounded query depth are proved in the manuscript.

No third-party paper, PDF, or font file is redistributed in this archive.

## 3. Novelty and verification boundary

The literature search was targeted, not exhaustive. It found the selected
repository problem and closely relevant primary graph-theoretic sources;
it does not certify priority. The proposed new contribution is the exact
local filter-profile classification, its capacity-attainment criterion,
the three-color separation, and the resulting ultrafilter threshold laws.

The directed pair-supersequence/feedback-set identity, the random-order
bound and the balanced-clique arc extremum are elementary proof ingredients
and are explicitly not claimed to be historically new as standalone results.

The mathematical theorems have self-contained conventional proofs, except
for the clearly identified standard NP-completeness input. No independent
refereeing, Lean proof, Rocq proof, or kernel audit has been performed.
The finite program tests the finite reductions, never an infinite filter.
See the exact ranges and limits in `results/verification.json` and Section
11 of the article. The README and article contain the same scope limits.
