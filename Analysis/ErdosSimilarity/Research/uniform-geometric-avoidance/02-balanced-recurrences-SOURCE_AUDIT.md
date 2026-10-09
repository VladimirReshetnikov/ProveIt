# Source audit: recurrence avoidance

## Snapshot and access

All repository inspection was read-only through the GitHub connector. The research package does not modify, merge, or publish a repository branch.

| Repository | Inspected revision |
|---|---|
| openai/math | adc7f1241b42e322a6451854ab7e4b4c146bf78a |
| VladimirReshetnikov/ProveIt | 58175ca45563d9ee29875374dd77942f069268a9 |

Retrieval date: 8 October 2026.

## Immediate predecessor

Directory at the ProveIt pin:

    Analysis/ErdosSimilarity/Research/uniform-geometric-avoidance/

The inspected manuscript already proves uniform geometric and positive-root exponential-polynomial avoidance and develops a rational-certificate viewpoint. Its further-questions section explicitly raises oscillatory recurrence sequences and suggests retaining several state coordinates. Those are the starting points of this continuation.

Inspected section blobs, as returned by GitHub at the pinned revision:

| Section | Git blob |
|---|---|
| sections/02_synchronization.tex | 21ed867f1bf9a94797f1c7d5752204bae3609636 |
| sections/03_routing.tex | e236813e3db249415da856b23baa8fcb55d5eb9b |
| sections/04_uniformity.tex | 653b1057ae05141ceabc5edd4986bba434cbd110 |
| sections/06_algebraic_families.tex | ba16f7690bb25bbf6dd1d4636699982d52b4d350 |
| sections/08_limits_and_questions.tex | 260b4566c59edde321d66d801cfade46b9db7e65 |

Other inspected metadata:

- uniform_geometric_avoidance.tex: 2abf6db8b813920c911424adac278c7aa7603ced
- SOURCE_AUDIT.md: 9f9701b8b84c39d4f728d412bd5cdab46913c015
- THIRD_PARTY_NOTICES.txt: 87e384819e48ab22b2b802c3ea2a7a381a7aa0a7
- LICENSE-APACHE-2.0.txt: 57bc88a15a0ee8266c259b2667e64608d3f7e292

## OpenAI family 084

Pinned directory:

    preprints/The-geometric-case-of-the-Erdos-similarity-conjecture-October-5-2026/build/

The introduction treats one fixed geometric ratio at a time; it does not state the new common recurrence theorem. The grid, ordered-window, first-default routing, conditional terminal independence, and residual-center repair arguments are the inherited mathematical construction. They are credited in the article and reproved for signed rational families.

Directly inspected section blobs:

| Section | Git blob |
|---|---|
| sections/01-introduction.tex | f5b867df4e87772187b0639de90b6a41626331d7 |
| sections/03-windows.tex | d409f3f9d8d8ace0318b47af74f1ea94e52060e4 |
| sections/04-routing.tex | f2b5233fa155e02eff559aadb238c6e881b69041 |
| sections/05-scales.tex | b9697d933e9798792eace89e3ef0f34d52c7e213 |

These are unrefereed repository sources. Reproving the required mechanism avoids making their main theorem an unstated input. This does not turn the present manuscript into a formally verified result.

## Primary literature and exact uses

- Basu, Pollack and Roy, *An asymptotically tight bound on the number of semi-algebraically connected components of realizable sign conditions*: https://arxiv.org/abs/math/0603256 . The finite bound in Section 3.2, equation (3.3), rather than only the leading asymptotic stated in the abstract, is the bound used in the proof.
- Basu, Pollack and Roy, *Algorithms in Real Algebraic Geometry*, second edition, Springer, 2006: https://link.springer.com/book/10.1007/3-540-33099-2 . The effective theorem uses decidability of first-order real-algebraic sentences.
- Burgin, Goldberg, Keleti, MacMahon and Wang, *Large sets avoiding infinite arithmetic / geometric progressions*: https://arxiv.org/abs/2210.09284 . This is context for the simultaneous-ratio question, not a proof of the present recurrence theorem.
- Jung, Lai and Mooroogen, *Fifty years of the Erdos similarity conjecture*: https://arxiv.org/abs/2412.11062 . Version 1, also inspected, has the earlier title *Some recent progress on the Erdos similarity conjecture*.
- Gao, Mooroogen and Yip, *On an Erdos similarity problem in the large*, Bulletin of the London Mathematical Society 57 (2025), 1801-1818: https://doi.org/10.1112/blms.70062 . This concerns a growing-sequence variant; it is not presented as a shrinking-pattern predecessor that already proves the new theorem.

## New assertions and limits

The substantive extension is simultaneous avoidance of all stable real C-finite patterns, including oscillations and exact zeros, and of the stated balanced P-recursive class. The proof additionally yields finite rational hitting certificates through compact outer approximants and a computable measure bound. It does not require root separation, a spectral decomposition uniform in the parameters, or a decidable test for stability.

The article does not claim the general Erdos similarity conjecture, all P-recursive null sequences, all infinite-dimensional families with comparable decay, a usable finite blocker size, or a computable distance function for the closed set.

The literature search and repository comparison are a bounded research audit. The claim is a full derivation of the stated mathematical results and a clear extension of the inspected source statements, not certified worldwide novelty or an externally reviewed breakthrough.

## Attribution

The top-level third_party directory retains the Apache 2.0 license text and the immediate predecessor's original notice for the inherited OpenAI construction. The package's THIRD_PARTY_NOTICES.txt identifies the changes in this continuation. Original source reports are referenced by immutable URLs rather than bundled in full.
