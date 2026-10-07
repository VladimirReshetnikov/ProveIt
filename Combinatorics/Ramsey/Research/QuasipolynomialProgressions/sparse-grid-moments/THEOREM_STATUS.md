# Theorem status and trust boundaries

Date: 2026-10-07. Version: research draft 1.

## Interpretation of status

“Written proof” means that a proof is supplied in this manuscript and was checked during its construction. It does not mean independent peer review, formal verification, or certified novelty. Exact finite checks provide reproducibility and error detection, not a proof of a statement quantified over all finite fields.

No statement below assumes the headline progression theorem in `openai/math`.

| Result | Status and role | Main dependencies |
|---|---|---|
| Theorem 2.3: exact polynomial relation code | Written proof; a precise finite-field formulation/generalization of the source coefficient-extraction mechanism | Coefficient extraction; coordinate exponents strictly below the characteristic |
| Proposition 2.5: full-grid rank | Written proof; standard tensor-basis dimension argument | Indicator-function basis; no division by axis sizes |
| Theorem 3.1: minimum support 2^(d+1) | Written proof; trade-type bound, not claimed as a new classical minimum-distance result | Slice induction |
| Theorem 3.2: minimum-support classification with exactly d+1 axes | Written proof; elementary product-code equality analysis | Line sums and slice induction |
| Theorem 4.3: sharp product-block mixing | Written proof; quantitative synthesis with exact spectral radius | Relation theorem, multilinear nonvanishing, Fourier/Parseval |
| Theorem 4.4: exact limiting moment Q^dim(K) | Written proof; explicit model law | Character expansion and positive block spectrum |
| Theorem 5.2: other p-reduced blocks | Written proof; weaker explicit mixing bound | Nonzero polarization; repeated Cauchy–Schwarz |
| Theorem 6.2: sharp cutoff variance obstruction | Written proof; standard Fourier/power-mean ingredients in this grid interface | One-dimensional cube relation; Parseval |
| Theorem 7.3: rank-one rigidity of the grid matrix span | Written proof; principal algebraic ingredient of the proposed new correction theorem | One-hot block zeros and equal block-sum contractions |
| Theorem 7.4: quadratic closure correction | Written proof; principal proposed original result, priority unestablished | Rank-one rigidity, bilinear character sum, exact normalization |
| Theorem 8.1: exact graph-girth convergence law | Written proof; proposed original local counting result, priority unestablished | Weighted Laplacian ranks, shortest-cycle recurrence, reciprocal-weight count |
| Corollary 8.2: exact moment of every even cycle | Written proof; explicit all-field/all-length formula | Forest ranks and weighted cycle kernel |
| Theorem 9.1: complete cube rank enumerator over all finite fields | Written proof; principal proposed original result, priority unestablished | Rank-two Gram counts in both characteristics; first kernel moment |
| Corollary 10.1: exact seven/eight-site moments | Written proof; exact quantitative consequence | Common seven-dimensional span and rank enumerator |
| Questions 12.1–12.8 | Open directions proposed here, not claimed solved | See article |

## Mathematical hypotheses that must not be dropped

1. A pattern is a set of distinct formal choice vectors. Randomly sampled values may coincide; those collisions are included.
2. The arbitrary-polynomial relation theorem assumes each coordinate exponent is below the **characteristic**, not merely below the field size. Over a prime field this is the usual reduced representative; over an extension field it is a stronger condition. The example z^p explains why formal degree alone is insufficient.
3. The sharp mixing rate and nonnegative spectrum concern the independent product-block model B_(d,n). The arbitrary-block theorem gives a weaker rate and does not assert positive Fourier coefficients.
4. The quadratic closure is relative to the stated ambient Cartesian grid.
5. The zero-level weights are normalized by their exact means. Omitting the mean changes the first correction.
6. The rank-one and rank-enumerator arguments use bilinear sums in two independent variable groups; they do not identify a characteristic-two quadratic polynomial with a symmetric form by dividing by two.
7. The graph-girth theorem concerns simple bipartite patterns in two axes. It counts all cyclic-support frequencies of minimal rank, not only frequencies supported on shortest cycles.
8. The classification of minimum-support relations in Theorem 3.2 assumes exactly d+1 axes. No complete classification for extra axes is claimed.

## Verified computational scope

The supplied JSON records a completed run over field orders 2, 3, 4, 5, 7. All 920,367 cube-space matrices and all 1,275 nonempty cube subpatterns in that run were checked. The rank-two and rank-three/four formulas nevertheless have general written counting proofs; the finite enumerations are independent checks.

The graph checks additionally enumerate 28,970 frequency assignments over F_2 and F_3, on cycles of lengths 4, 6, and 8, K_(2,3), K_(3,3), and a five-edge path. Their first nonzero error degrees are respectively 2, 4, 6, 2, 2, and none (exact equality for the path).

The direct n=1 checks yield:

| Q | Seven-site normalized moment | Eight-site normalized moment |
|---|---|---|
| 2 | 320/243 | 1280/729 |
| 3 | 152361/78125 | 1371249/390625 |

No Lean, Rocq, or other proof-assistant build was performed. No external independent reviewer was consulted. No tests over F_8 or F_9 are claimed in the recorded output.

## Source and novelty boundaries

The OpenAI source explicitly restricts its bounded-grid lemma to q ≤ j. The present obstructions outside that range are not a refutation of the source's stated lemma. Nor do the finite-field results verify its torus geometry, rank estimates, inverse-theorem applications, or global arithmetic-progression bounds.

The relation-code viewpoint overlaps classical tensor independence, trades, and low-degree codes. The closure correction, graph-girth moment law, and full cube rank enumerator were derived in this session. Targeted searches did not find their exact statements, but a limited search cannot establish priority. Independent review and a broader literature comparison remain necessary before publication-level novelty claims.
