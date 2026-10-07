# Sources and claim boundaries for Report278

This report gives written proofs of its mathematical statements. External references supply attribution and comparison; neither finite diagnostics nor a limited literature search establishes priority or formal correctness.

## Direct preceding reports

- Report277, *Threshold free polynomial density increments on cyclic groups*, 6 October 2026. The inspected article source has SHA-256 `3d22346ebb60e2c8829236ee05e9ba5a0bd6cd8c8241199cca17445dcefe9f5d`. Section 5 averages all directions and removes short-order directions using a bound at most L(L-1)/(2N), obtaining gain (1-delta)/(2L) under N >= L^3. Report278 replaces that standalone sufficient condition by N >= 2(L-1)^2+1 and proves the stronger largest-small-divisor formula. The separate all-degree phase exponents are unchanged
- Report275, the preceding threshold-free affine density-increment report. The inspected source has SHA-256 `10ff1fbf1c43a8f0ba9e9e17e6756872b0f4eb49de707cfcd5238028680cff35`. Its theorem “Threshold free cube root bound” and section “The cube root bound” use x = min{(r(1-delta)/(128 mu))^(1/3), (N/8)^(1/3)}. The new affine consequence replaces only the second cap by sqrt(N/2), with the first term and gain alpha/3 unchanged. Report277 retains the earlier affine statement

The earlier reports are not needed to follow the new proofs, and no earlier report was modified in preparing this package. Their source hashes identify the exact compared versions; a hash alone is not an authorship or mathematical-validity certificate.

## Classical and contemporary mathematical references

1. Rajendra Bhatia and Chandler Davis, “A Better Bound on the Variance,” *American Mathematical Monthly* 107 (2000), 353–357. DOI: https://doi.org/10.1080/00029890.2000.12005203 . The elementary inequality Var(Y) <= E(Y)(M-E(Y)) for 0 <= Y <= M is its lower-endpoint-zero case. The proof is included in Report278. Publisher bibliographic metadata was checked; no use of an unseen proof is required
2. Mihail N. Kolountzakis and Szilárd Gy. Révész, “Turán’s extremal problem for positive definite functions on groups,” arXiv:math/0312218, first version 10 December 2003; author PDF October 2004 version: https://eigen-space.org/ps/turan-groups.pdf . Theorem 2 and Section 3.2 directly support the packing bound and autocorrelation equality mechanism. Taking the packing set to be the subgroup of size m yields sum w <= (N/m)w(0), hence w(0) >= 1/q for a probability weight. This is a specialization of a classical result, not a new extremal principle
3. Jacob Fox, Max Wenqiang Xu and Yunkun Zhou, “Discrepancy in Modular Arithmetic Progressions,” primary preprint arXiv:2104.03929v1, 8 April 2021: https://arxiv.org/html/2104.03929v1#S4 . Published in *Compositio Mathematica* 158 (2022), 2082–2108. Section 4, particularly Lemmas 4.2–4.3 and Corollary 4.4, treats fixed-length second moments, Fourier weights, subgroup sums and short-order corrections. It is a close neighboring mechanism. Its inspected statements concern two-sided discrepancy with progression lengths varying; this is not a proof that none of its consequences could overlap Report278
4. Mark Lewko, “A Fourier-Free Density-Increment Proof of Roth’s Theorem,” arXiv:2605.19310v1, 19 May 2026: https://arxiv.org/html/2605.19310v1 . Lemma 2 and Section 5, Lemmas 6–7, provide a close contemporary illustration of autocorrelation sums of squares, progression second moments, and zero-step removal. The density-increment argument has a prime-modulus setting and an additive-energy premise. Standard moment methods and zero-step subtraction are not claimed to originate in this report
5. W. T. Gowers, “A new proof of Szemerédi’s theorem,” *Geometric and Functional Analysis* 11 (2001), 465–588: https://sites.math.rutgers.edu/~zeilberg/akherim/GowersMasterpiece.pdf . Section 5 supplies the polynomial localization and transfer context of the preceding reports. The present variance theorem alone does not improve a global quantitative Szemerédi or Ramsey bound
6. Terence Tao, Math 247B Lecture Notes 9: https://www.math.ucla.edu/~tao/247b.1.07w/notes9.pdf . Fourier inversion, finite-group positive definiteness, and the finite-abelian Poisson formula are standard; see Corollary 1.8, Theorem 2.1 and Exercise Q1. Report278 proves the short subgroup calculation directly with declared normalization

## Pinned repository comparison

The bounded comparison inspected the ProveIt research article and README at commit `b16ce380d7b82557b7120ca56c0a78391fdaf35e`:

- Article: https://github.com/VladimirReshetnikov/ProveIt/blob/b16ce380d7b82557b7120ca56c0a78391fdaf35e/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/article.tex
- Source-10 variance-to-density calculation, lines 4804–4846: https://github.com/VladimirReshetnikov/ProveIt/blob/b16ce380d7b82557b7120ca56c0a78391fdaf35e/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/article.tex#L4804-L4846
- README: https://github.com/VladimirReshetnikov/ProveIt/blob/b16ce380d7b82557b7120ca56c0a78391fdaf35e/Combinatorics/Ramsey/Research/GowersSzemeredi/local-quantitative-refinements/README.md

At that pin, the README lists sources 01–14 as integrated and sources 15–23 as staged. The integrated article was retrieved and searched, and its closest relevant sections were read. Staged sources 16–17 were retrieved and their relevant manuscript sections inspected; sources 18–19 were compared using previously retrieved manuscripts. Sources 15 and 20–23 were screened through README, placement records and indexed code, not by a complete independent rereading of every proof. Indexed search sometimes returned an older commit; the direct pinned reads took precedence.

The integrated source-10 text already gives M >= delta + Var(X)/delta and explicitly treats it as an elementary bounded-variable inequality. Staged source 17 includes a Fejér filter for polynomial restriction. No exact fixed-length proper-progression tradeoff was located in the relevant inspected text. This bounded negative finding is not a priority certificate, and this work does not confer Lean status on any theorem.

## Literature-screen limitations

K. F. Roth’s “Irregularities of sequences relative to arithmetic progressions” and Part II, *Mathematische Annalen* 169 (1967), 1–25 and 174 (1967), 41–52, are relevant classical leads. Their DOI records were checked:

- https://doi.org/10.1007/BF01399529
- https://doi.org/10.1007/BF01363122

The original full texts were not retrieved in the bounded screen. The related one-sided fixed-length results were inspected through the expert survey by A. Sárközy and C. L. Stewart, “Irregularities of sequences relative to long arithmetic progressions,” Theorem 6: https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/roth.pdf . That secondary account involves a sufficiently large threshold depending on density and length. Report278 makes no claim to have rechecked Roth’s original proof or to have completed an exhaustive priority search.

## Scope of optimality

- The admissible iid support has exactly optimal cardinality q, and the corresponding positive-definite proper-support probability weight has exactly minimum zero mass 1/q
- The arithmetic density bound is attained on the stated prime-quotient family, but is not asserted to be optimal for every fixed pair (N,L) and density
- The quadratic coefficient 1-1/C is optimal uniformly over all nontrivial densities. Its extremizing sequence has density tending to zero
- The separate sliding-window theorem gives H > delta(1-delta)/(2L) for N > L(L-1), and a more precise bound using the proportion of short-order directions. Dense prime-boundary pullbacks show the strict size threshold is sharp even for densities approaching any prescribed value in (0,1). No optimality of the quantitative endpoint coefficient is asserted
- Modular wrapping and nonunit steps are allowed. No ordinary-integer rectification or parent containment follows from the variance theorem
- The affine application changes an independent modulus cap. It does not change the separate polynomial phase exponent or prove a global Ramsey/Szemerédi improvement
- The companion is a bounded exact diagnostic program, not a universal proof or formal certificate
