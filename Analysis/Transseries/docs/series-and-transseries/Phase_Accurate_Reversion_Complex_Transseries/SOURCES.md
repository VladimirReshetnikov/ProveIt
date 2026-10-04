# Sources and provenance

Review date: 4 October 2026. This is a bounded source and overlap review, not an exhaustive novelty search.

## Repository

Repository: https://github.com/VladimirReshetnikov/ProveIt

The initial GitHub tree response identified revision:
`8e9cd6f00e0ac79c4425ff6abdfa64b497cf3f41`.

Directly read at that pinned revision:

`Analysis/Transseries/docs/series-and-transseries/Support_Controlled_Reversion_One_Exponential/reversion_and_one_exponential.tex`, source lines 380–600. This includes the Newton theorem `thm:newton`, equation `eq:newtonrate`, and editorial note `ed:newton-depth`. The pre-existing depth `2^(k+1)-1` is explicitly credited in the new article.

Also read through the GitHub connector on the default branch:

- `Analysis/Transseries/README.md`.
- `Analysis/Transseries/docs/series-and-transseries/README.md`, introduction and the relevant arrival/comparison sections.
- `Analysis/Transseries/docs/series-and-transseries/Nonlinear_Stokes_Transport_Logarithmic_Inversion/README.md` (returned blob `3843e5292a24c9119c3901c3254af191fe40c418`).

The non-Archimedean package's relation to the Newton rate was examined through the collection index and the explicit editorial comparison in the pinned support-controlled source. Its full proof was not independently reread. Likewise, the nonlinear Stokes package README establishes the declared scope of the relevant overlap; the new article supplies its own proof of the transport formula it uses.

The entire canonical volume and every unmerged arrival were not exhaustively reread. No claims of complete repository coverage or world-first priority are made. No repository file was edited.

## Primary external literature

1. Ira M. Gessel, *Lagrange inversion*, J. Combin. Theory A 144 (2016), 212–249. DOI: 10.1016/j.jcta.2016.06.018. Author preprint: https://arxiv.org/abs/1609.05988
2. Joris van der Hoeven, *Transseries and Real Differential Algebra*, LNM 1888, Springer, 2006. DOI: 10.1007/3-540-35590-1. Author page: https://www.texmacs.org/joris/ln/ln-abs.html
3. Joris van der Hoeven, *Complex transseries solutions to algebraic differential equations*, report 2001-34, Université Paris-Sud, 16 November 2001; corrected author-hosted version: https://www.texmacs.org/joris/osc/osc.html
4. David Sauzin, *Nonlinear analysis with resurgent functions*, Ann. Sci. ENS (4) 48(3) (2015), 667–702. DOI: 10.24033/asens.2255. https://numdam.org/articles/10.24033/asens.2255/
5. David Sauzin, *Introduction to 1-summability and resurgence*, 2014. https://arxiv.org/abs/1405.0356

These works are cited for established background, not presented as results of this article. In particular, suitable resurgent and Borel–Laplace classes already have nonlinear inversion theorems. Their hypotheses are not replaced by a general assertion of formal invertibility.

## Proposed refinements

The manuscript proves its own stated phase-normalization formulas, exact power-core Newton constants, fixed and moving precision thresholds, higher-height finite-jet obstruction and cutoff, and the accompanying explicit consequences. Independent novelty assessment is still required. Classical ingredients and elementary consequences are labeled as such in Appendix D.
