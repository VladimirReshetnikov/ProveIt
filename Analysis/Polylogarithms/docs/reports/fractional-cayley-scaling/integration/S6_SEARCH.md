# S6 search outcome and a concrete next step

The frozen target is the depth-two identity recorded in the pinned canonical `04-cyclotomic-quotients.tex`, reproduced as a conjecture in the article. Its equivalence with the alternate Gaussian basket is already proved upstream.

An exploratory weight-seven construction generated 51,244 normalized double-shuffle rows on 24,514 imaginary admissible word coordinates, with roughly 2.08 million nonzero entries, and then added a selected convergent Cayley seed. Sparse elimination suffered substantial fill-in and was stopped. It produced neither:

- a rational combination proving the target;
- a completed rational nonmembership calculation;
- nor a separating functional.

The unfinished matrices and imported older search implementation are not included because none of the new theorems depends on them. The search counts describe the exploration, not a new rank certificate.

The positive output is the all-weight Cayley theorem. Its full shuffle ideal reduces the formal imaginary weight-seven quotient to 7,518 coordinates. A principled next attempt should construct simultaneous Cayley/conjugation eigenvector generators and exact reconstruction maps before introducing double shuffle. This avoids treating raw Cayley rows as their multiplicative closure and supplies a defined route to a final exact residual certificate.

The explicit 96-term high-depth identity in `data/cayley/S6_cayley_depth_seven.json` is proved and independently regenerated. It should be retained as a normalization and transport check in any future reduced-basket search.
