# Source and claim audit

Research and source checks performed on 30 September 2026.

## 1. Direct repository baseline

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `a4268e78ebd0f6bf71ba609c07f4b3415748f532`.

Main source:

```
SetTheory/Cardinals/docs/reports/ordinals-and-order-types/
games-on-ordinals/open-query-membership-games/article.tex
```

Article blob: `d1e50fd006a8ba1fe645b41b4fb37ee35f7043fe`.

Permalink:
https://github.com/VladimirReshetnikov/ProveIt/blob/a4268e78ebd0f6bf71ba609c07f4b3415748f532/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/games-on-ordinals/open-query-membership-games/article.tex

The corresponding directory README was read through the connected GitHub tool, together with the following explicit line ranges of the pinned article:

| Lines | Relevant content |
|---|---|
| 500–640 | Binary oriented closures; finite-height classification and derivative descent |
| 1150–1360 | Finite verification; scope; Part II provenance and contribution list |
| 1480–1690 | Binary crosswalk; finite-output definitions; Theorem 16.2 tree–layer normal form; Proposition 16.3 closure elimination |
| 2100–2340 | Synchronization; exact word bounds; finite examples; SCS complexity context |
| 2640–2800 | Dependencies and formalization; Research question 1 and Part III's finite-derived-set answer; remaining higher-height/infinite-derived issues; obstruction-size question and prior bound |
| 3780–3970 | Ultrafilter/convergent-sequence comparison; finite-derived-set local hypotheses and capacity formula; graph extremal discussion |

The root README and repository search results were used to select a relevant direction. They are not treated as proof of unrelated research claims. This was a targeted review of the indicated program, not an audit of the complete repository.

### Reused and extended material

The source already proves the finite tree–layer normal form, fixed-word closure elimination, finite-poset chain interpretation, compact single-word realization, universal reduced-word constant, and the finite-derived-set graph mechanism. These are credited and, where used, reproved in the new article.

The new manuscript develops the universal nested-closure signature; full and truncated duality; recoverability of bounded signatures; complete finite-depth word-equivalence classification; optimal Hausdorff representative height; extension of the graph formula to arbitrary first-derivative cardinality when the second derivative is empty; improved finite-budget and subposet bounds; a product signature/rank law; and matched-space higher-order examples.

The exact scope of the answer to the repository's Research question 1 is **the fixed-coloring profile problem**. The possible signatures of all colorings of a fixed space, sharp local capacity criteria at greater heights, and general transfinite games remain separate questions.

## 2. Primary public literature checked

### Chiozini, Csernák, Soukup

Lucas Chiozini, Tamás Csernák, Lajos Soukup, *Cut-and-choose games in topological spaces*, arXiv:2510.05754v3.

- https://arxiv.org/abs/2510.05754v3
- https://arxiv.org/html/2510.05754v3
- DOI: 10.48550/arXiv.2510.05754

The arXiv metadata identifies v3 as 29 May 2026, with first submission on 7 October 2025. The abstract metadata and available HTML were consulted for the original game framework and its questions. The current abstract-page title is used; the rendered HTML has also circulated with an earlier title. No result of the new paper is presented as a general solution of the authors' transfinite or supremum-over-colorings questions.

### Lagoutte, Tavenas

Aurélie Lagoutte, Sébastien Tavenas, *The complexity of Shortest Common Supersequence for inputs with no identical consecutive letters*, arXiv:1309.0422v2.

- https://arxiv.org/abs/1309.0422v2
- DOI: 10.48550/arXiv.1309.0422

Current metadata and abstract checked: v2 is 8 January 2015, first submission 2 September 2013. The abstract states the NP-completeness of the pertinent variants for alphabets of size at least three. This is related-work and complexity context only; no new structural theorem in the manuscript depends on an imported hardness proof.

### Selivanov

Victor Selivanov, *Towards a Descriptive Theory of cb_0-Spaces*, arXiv:1406.3942, 16 June 2014.

- https://arxiv.org/abs/1406.3942
- DOI: 10.48550/arXiv.1406.3942

The indexed primary arXiv abstract was available and consulted. Direct opening of the abstract URL returned a retrieval error; the paper's full text was not reviewed. The abstract supports the stated context of finite partitions, difference hierarchies, fine hierarchies, and Wadge-related questions. No detailed comparison theorem or equivalence is attributed to it.

## 3. Novelty and reliability boundary

The manuscript gives complete written proofs of its mathematical claims. “New here” means a substantive extension relative to the inspected baseline, not independently certified historical priority. The literature checks are targeted rather than exhaustive. The manuscript is unrefereed and has not been formalized in a proof assistant.

The finite verifier is original package code. Its output records completed tests, not a proof of infinite topological assertions. All compactness, derivative, realization, and general duality claims depend on the written arguments, not on extrapolation from small finite examples.

The package does not contain or redistribute copies of the cited external papers or the repository report, and it does not modify the repository.
