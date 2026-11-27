# Proposed Lean formalization plan (not implemented or compiled)

The following is a mathematical dependency specification, not executable Lean. The existing GRH proof is used only at the analytic bridge. The finite count certificate can be formalized independently of analytic number theory.

## A. Finite algebra

- Define `B(n,k,t) = ∑ r ∈ Icc k n, (n.choose r : R) * t^r * (1-t)^(n-r)` for a field of characteristic zero.
- `D(t) = ∏ i, (1 + d i * t)`, for pairwise distinct nonzero `d` on `Fin n`.
- Define `c i` from equation (4) of the paper (the displayed coefficient formula).
- Prove the polynomial identity `B = ∑ i, C (c i) * X * ∏ j ∈ univ.erase i, (1 + C (d j) * X)`. The difference has degree ≤ n and n+1 distinct roots (0 and -1/d i). This avoids division of polynomials and handles n=1 directly.
- Evaluate at t and divide by the positive D(t) for t in [0,1].

## B. Pointwise inequalities and summable measure

- Prove binomial mass ≥0, total mass =1 via binomial theorem, and monotonicity of tails (e.g. finite independent Bernoulli coupling or polynomial derivative identity).
- `k * B n k t ≤ n * t * B (n-1) (k-1) t` follows from `r * choose n r = n * choose (n-1) (r-1)` and the finite sum inequality.
- Abstract data: `t : ι → ℝ`, `0 < t i ∧ t i ≤ 1`, `Summable t`, `τ ∈ Ioo 0 1`, `d : Fin n → ℝ` positive and injective.
- The support above τ is finite because each atom contributes ≥τ and the sum is finite. Use `tsum_le_tsum` for the signed minorant (absolute summability from O(t)) and majorant; derive bounds on the cardinality of finite supports. Integer ceiling/floor and nonnegative count give the exact certificate rule.
- Prove convergence via binomial variance or a Chernoff/Hoeffding bound and dominated convergence for summable families. Treat exact threshold separately: lower limit strict, upper inclusive.

## C. Analytic interface

A useful target bridge is: for each primitive Dirichlet character χ, construct a multiset/family of zeros in the critical strip counted by orders of vanishing, with real ordinates γ under GRH; prove `Summable (fun j => 1/(a + γ j^2))` and the exact formula `∑' j, 1/(a + γ j^2) = Re (Gχ'/Gχ)(1/2 + sqrt a)/sqrt a` for positive real a. Include pole removal at conductor 1, even paired completion, the zero at the center, and primitive reduction for imprimitive χ. This likely needs new formal entire-function/Hadamard-product infrastructure; do not assume it is in Mathlib merely because GRH is formalized.

Reuse the repository's `DirichletLZerosOnLine` (or `PrimitiveDirichletLZerosOnLine`) through its exported theorem, and standard definitions of `riemannZeta` and `DirichletCharacter.LFunction`. The theorem interface for the half-plane in `Statements.lean` is `DirichletLNonvanishingRightOfHalf`. The source builds with standard axioms according to the repository and independent reports. No new theorem in this package has been kernel-checked.

## D. Numerical verification

The final bracket is exact rational arithmetic and can be replayed by a small Lean checker given rational interval hypotheses. A fully kernel-checked numerical certificate must also establish the analytic input intervals, including correct bounds on sqrt, exp, log, digamma and the eta-series tail; the shipped Python code uses Python Decimal for elementary function enclosures instead. The exact arithmetic tests do not replace the proof of the infinite-sum result.
