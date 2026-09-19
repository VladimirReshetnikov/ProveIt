# Source, hypotheses, and research status

Access and manuscript date: September 19, 2026.

## Target

Richard Stanley, **A conjectured rational generating function**,
MathOverflow question 431075, posted September 23, 2022.

https://mathoverflow.net/questions/431075/a-conjectured-rational-generating-function

The source assumes positive integer exponents G_n tending to infinity and
rationality of their ordinary generating function. It asks about rationality
of the generating function for the number of polynomial coefficients equal
to a fixed positive integer. The binomial factors are explicitly included.

The displayed question does **not** impose increasing exponents, distinct
exponents, or nonnegative coefficients in a recurrence. The construction in
this archive uses this distinction: all exponent terms are positive and tend
to infinity, but the interleaved sequence is not eventually increasing.

The source page displayed no posted answer when retrieved. Searches for the
exact title and author/coefficient-count/rationality/counterexample combinations
did not locate a prior resolution of this unrestricted formulation. This is a
limited status check, not an exhaustive literature search or a guarantee of
priority. Correctness is supported by the written argument, not by the absence
of a previously located answer.

## Related primary sources

1. Richard Stanley, **Number of coefficients equal to k in certain
   “Fibonacci polynomials”**, MathOverflow question 430741,
   September 19, 2022.
   https://mathoverflow.net/questions/430741/
   This earlier special question is not the assertion disproved here.

2. Richard P. Stanley, **Theorems and conjectures on some rational generating
   functions**, arXiv:2101.02131v3, September 30, 2021.
   https://arxiv.org/abs/2101.02131v3
   Background on products involving Fibonacci and related exponent sequences.

3. Richard P. Stanley, **Differentiably finite power series**,
   European Journal of Combinatorics 1 (1980), no. 2, 175–188.
   https://www.sciencedirect.com/science/article/pii/S0195669880800515
   Background on D-finiteness and polynomial-coefficient recurrences. The
   obstruction used in the article is explained directly in the proof.

## What the manuscript establishes

- An explicit positive C-finite exponent sequence tending to infinity.
- An exact formula for unit-coefficient counts, proved by support convolution.
- Nonperiodicity of the resulting bounded count sequence, hence nonrationality.
- A natural boundary via dense, nonzero Fourier–Abel radial limits.
- Nonalgebraicity and non-D-finiteness, but not differential transcendence.
- Asymptotic, density, correlation, general-control, and rescaling statements.

## What is not claimed

The manuscript has not undergone independent peer review or formal proof-assistant
verification. Finite code checks are independent checks of finite instances, not
formal certificates of the infinite result. No full classification is supplied,
and no increasing-exponent variant is settled. No OEIS entry or public answer
has been submitted as part of this work.
