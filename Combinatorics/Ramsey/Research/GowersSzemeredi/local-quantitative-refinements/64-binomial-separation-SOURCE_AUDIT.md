# Sources, comparisons, and audit boundaries

Date of manuscript: 6 October 2026 (Pacific time).

## Repository inspection

The requested scope was
https://github.com/VladimirReshetnikov/ProveIt/tree/main/Combinatorics/Ramsey .
The Ramsey directory, the research tree, the local-quantitative-refinements
README, and topic-targeted GitHub searches were inspected. Those searches
showed a substantial collection of local quantitative research, rather than a
single unmodified Gowers proof. This report therefore targets the Section 4
uniformity/progression-count program and its binomial-separation interface.

The exact file read for the Section 4 interface was
`Combinatorics/Ramsey/Lean/GowersSzemeredi/Section04.lean`, blob
`987daf1643df5bd45a9e9202a08fb2f7c579a103`.
It explicitly describes the conjectures as non-asserting proposition-valued
definitions. Its `conjecture_4_2` uses progression length `k+2`.

Search-result snapshots included commits
`17123532a2de638477dce1c92eb0b0b20a247d2f` and
`176e155e51add237f31ac8e057fe5db46d6aef26`. These are search snapshots, not a
claim that the entire repository was checked at either immutable commit.
The repository was changing during inspection. No matching prior report for
the specific seed and endpoint chain was surfaced by the targeted searches;
that is not a certified repository-wide nonduplication result.

## Primary mathematical sources

### Gowers (2001)

W. T. Gowers, *A new proof of Szemerédi's theorem*, GAFA 11 (2001), 465–588.
DOI: https://doi.org/10.1007/s00039-001-0332-9 .

Relevant repository materials are the PDF and TeX transcription under
`Papers/sz-thm-gowers-proof/`, and the Section 4 declarations above.
The new manuscript concerns the conjectural uniformity/counting issue, not a
claimed new proof of the full Szemerédi theorem.

### Gowers (2020)

*A uniform set with fewer than expected arithmetic progressions of length 4*.
https://arxiv.org/abs/2004.07598
DOI: https://doi.org/10.1007/s10474-020-01072-z .

The article's known four-term counterexample is explicitly credited. Its
existence is not presented as a new result of this package.

### Deng–Tidor–Zhao (2025)

*Uniform sets with few progressions via colourings*.
https://arxiv.org/abs/2307.06914v2 (15 May 2025).
Journal version: Math. Proc. Cambridge Philos. Soc. 179(1) (2025), 79–103.
DOI: https://doi.org/10.1017/S0305004125000106 .

Inspected definitions and statements: Definition 1.11; Proposition 2.2;
Proposition 2.4; Definition 3.4; Lemmas 3.3, 3.6, 4.2, 4.3; Theorems 2.7–2.8;
and the role of the equidistribution appendix. PDF pages containing the beta
convention and relevant reduction formulas were visually inspected.

The definition of beta is reciprocal growth: a label set has size at least
`N^(1/beta-o(1))`. The new proof uses the unambiguous modulus convention
`m_R <= C R^b` throughout; it does not import intermediate exponent displays
from the proof of Theorem 2.8. The generic source bound supplies `b=5` at
length six. The existing four-variable base-9 alphabet is credited.

The new circle theorem controls only full mirror symmetry. It is not asserted
that nine copies control every broader binomial color pattern in Lemma 4.3.
Mirror separation of the labels is an explicit hypothesis. At length six,
its equivalence with the absence of nontrivial solutions is proved from the
distinct subset sums of `(1,5,10)`.

### Shi–Dong (2026)

R. Shi and Y. Dong, *An Improved Upper Bound for Colorings Without
Symmetrically Colored k-Term Arithmetic Progressions*.
https://arxiv.org/abs/2607.20752v2 (28 July 2026).
The inspected PDF is dated 30 July 2026. This is treated as a preprint.

Theorem 1.1 supplies `(k-1)^(k^2/4-1) p` colors on `Z/p^(k^2/4)Z` for primes
`p>k`. The paper's stated four-term consequence has exponent `5-epsilon`.
Its general even-length consequence and the prime-family construction were
checked in the PDF; the application page was also visually inspected.

This package credits that coloring family and the even-length counterexamples.
Its new argument uses the prime family directly at the density-dependent
scale, rather than first fixing a prime and then taking a tensor-power limit.
The degree-restricted dimension barrier is a proved sharpening within the
specified model, not a claim against all polynomial or nonpolynomial methods.

### Weighted-Sidon background

M. B. Nathanson, *Sidon sets for linear forms*, J. Number Theory 239 (2022),
207–227, https://arxiv.org/abs/2101.01034 ,
https://doi.org/10.1016/j.jnt.2021.08.005 .

Y. C. Cheng, *Greedy Sidon sets for linear forms*, J. Number Theory 266 (2025),
225–248, https://doi.org/10.1016/j.jnt.2024.07.010 .

These sources establish the terminology and the existing digital-construction
context. Cheng's publisher preview was inspected for background only; no
technical result from it is required by the new proofs.

## Claim boundaries

The seed injectivity, lifting, interval bounds, valuation obstruction,
nine-copy transfer, exact slice computation, endpoint theorem and
polynomial-dimension barrier all have proofs in the manuscript. The passage to
cyclic indicator sets is also proved in the specialized prime-modulus setting.
The sole advanced combinatorial construction imported in the final endpoint
corollaries is the credited Shi–Dong family (besides standard background
algebra, harmonic analysis, and the prime interval theorem).

Neither beta_6=3 nor superpolynomial decay of rho_4 or rho_6 is proved. No
single-seed optimality claim is made. The perfect-code obstruction excludes
only equality B=r^3 in a cyclic alphabet; it does not exclude a sequence of
near-perfect alphabets or an optimal-order nondigital construction.

Web and repository searches were targeted, not exhaustive. Therefore the
appropriate priority description is: explicit proved improvements over the
specified inspected bounds, proposed for independent mathematical review.
Third-party papers, repository files, exploratory search binaries, and font
files are not redistributed in the package.
