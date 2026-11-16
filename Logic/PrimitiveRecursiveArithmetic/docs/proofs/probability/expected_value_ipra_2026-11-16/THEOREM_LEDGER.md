# Theorem ledger: Wikipedia "Expected value"

Status codes:

- **E** - exact finite theorem, directly reducible to primitive-recursive bounded sums and quantifier-free induction.
- **M** - effective-modulus theorem: an iPRA theorem schema for a fixed primitive-recursive presentation carrying the stated modulus/certificate.
- **A** - analytic corollary of the effective integration/regular-real library; the manuscript supplies the reduction and explicit estimates.
- **C** - constructive counterexample or correction/audit.
- **R** - classical existence statement replaced by a witnessed/effective formulation; no uniform constructive converse is claimed.
- **H** - historical or notational prose, not a mathematical theorem.

The PDF theorem numbers are the authoritative cross-reference.

## Definitions and introductory claims

| ID | Article claim | Status | Constructive result in this packet |
|---|---|---:|---|
| EV-001 | Expectation generalizes a weighted average. | E | Thms. 3.3--3.4: exact natural-weight/rational-value weighted-average formula and convex-hull bounds. |
| EV-002 | Finite expectation is `sum x_i p_i`. | E | Def. 3.1 and Thm. 3.3 after common-denominator normalization. |
| EV-003 | Probabilities sum to one. | E | Def. 2.2 supplies `sum w_i = W`; Thm. 3.2 proves `E[1]=1`. |
| EV-004 | Equiprobable expectation is the arithmetic mean. | E | Cor. 3.5, cross-multiplied to avoid division. |
| EV-005 | Vector and matrix expectations are componentwise. | E | Thm. 3.9; finite products of coordinates are primitive recursive. |
| EV-006 | Long-run averages converge to expectation. | M | Thms. 8.4--8.6: weak law and an explicit finite-horizon strong-law contract via Kolmogorov's inequality. |
| EV-007 | General expectation is a Lebesgue integral. | R/M | Sec. 10 replaces arbitrary measure objects by effective refining simple-law names; Thm. 10.3 constructs the expectation regular name. |
| EV-008 | Lebesgue integration is built from finite-valued approximants. | M | Def. 10.2 and Thm. 10.3 formalize precisely this effective core. |

## Finite examples

| ID | Article claim | Status | Constructive result |
|---|---|---:|---|
| EV-010 | Fair die has expectation `3.5`. | E | Ex. 4.1: `E[X]=7/2`. |
| EV-011 | American straight-up roulette has expected gain `-1/19` dollars. | E | Ex. 4.2, exact rational calculation. |
| EV-012 | In 190 such bets the expected net loss is 10 dollars. | E | Linearity gives `190*(-1/19)=-10`; probabilistic concentration is separately bounded. |

## Countable outcomes and series

| ID | Article claim | Status | Constructive result |
|---|---|---:|---|
| EV-020 | Countable expectation is an infinite weighted sum. | M | Def. 9.3, built on Def. 9.1: regular expectation from rational partial sums plus an absolute-tail modulus. |
| EV-021 | Absolute convergence makes the sum independent of order. | M | Thm. 9.4: reindexing invariance with a primitive-recursive coverage modulus. |
| EV-022 | Conditional rearrangements may change the sum. | C/A | Prop. 9.5 and Thm. 9.6: alternating harmonic order gives `ln 2`; the `++-` rearrangement gives `3/2 ln 2`. |
| EV-023 | Example `p_i=(1/ln2)/(i2^i)` has mean `1/ln2`. | A | Prop. 9.7 with explicit geometric tails and a regular reciprocal of `ln 2`. |
| EV-024 | A nonnegative countable variable has an extended expectation. | M | Def. 9.8: increasing partial expectations define a lower real; a regular real is obtained when a tail modulus exists. |
| EV-025 | St Petersburg expectation is `+infinity`. | E/M | Prop. 9.9: the first `N` terms have expectation exactly `N`, hence explicit divergence. |
| EV-026 | Positive and negative parts satisfy `X=X^+-X^-`. | E | Lemma 5.8, pointwise signed-integer identity. |
| EV-027 | Extended expectation is classified by the two parts. | M | Def. 9.10 and Prop. 9.11. |
| EV-028 | The alternating `1,-2,3,-4,...` example is undefined. | A | Prop. 9.12; both part expectations dominate divergent odd/even harmonic sums. The Basel normalization is isolated as an effective analytic dependency. |

## Densities, CDFs, and tail formulas

| ID | Article claim | Status | Constructive result |
|---|---|---:|---|
| EV-030 | For a density, `E[X]=integral x f(x) dx`. | A | Def. 10.9 and Thm. 10.11 using compact quadrature and an improper-tail modulus. |
| EV-031 | Piecewise-continuous densities may be handled by Riemann integration. | A | Thm. 10.6 for compact pieces, extended by Def. 10.7 and Thm. 10.8 to improper integrals. |
| EV-032 | Cauchy principal-value style truncations are ambiguous. | C/A | Prop. 10.17 computes the two truncation paths (`0` versus `(ln 2)/pi`) and proves failure of absolute integrability. |
| EV-033 | Density and general integral definitions agree. | M/A | Thm. 10.10: the simple-law approximants induced by rational grids have the same regular expectation. |
| EV-034 | The four classical absolute-continuity conditions are equivalent. | R | Prop. 10.15 proves the forward consequences of an explicit density witness; no non-effective Radon--Nikodym converse is asserted. |
| EV-035 | LOTUS for a density: `E[g(X)]=integral g f`. | A | Thm. 10.11, with a modulus for `g f` and tails. |
| EV-036 | CDF/Stieltjes representation. | M/A | Thm. 10.13 gives the effective integration-by-parts version for certified bounded-variation/CDF names. |
| EV-037 | Area balance characterization of the mean. | A | The area-balance conclusion is the final clause of Thm. 10.14. |
| EV-038 | Signed tail formula for general integrable `X`. | M/A | Thm. 10.14 from positive/negative layer-cake formulas. |
| EV-039 | Nonnegative tail integral `E[X]=int_0^infty P(X>t)dt`. | E/M/A | Finite layer-cake Thm. 5.16; effective limit Thm. 10.14. |
| EV-040 | Nonnegative integer tail sum `E[X]=sum P(X>k)`. | E/M | Thm. 5.14 for bounded variables and Cor. 9.13 with a tail modulus. |
| EV-041 | Mixed precipitation model has mean `alpha/lambda`. | A | Prop. 11.10: atom at zero plus exponential survival integral. |

## Common distributions

| ID | Distribution claim | Status | Constructive result |
|---|---|---:|---|
| EV-050 | Bernoulli mean is `p`. | E | Prop. 11.1. |
| EV-051 | Binomial mean is `np`. | E | Prop. 11.2, both by linearity of Bernoulli sums and by the binomial identity. |
| EV-052 | Poisson mean is `lambda`. | A | Prop. 11.3, shifted exponential series with factorial tail modulus. |
| EV-053 | Geometric mean is `1/p`. | M/A | Prop. 11.4, finite geometric-derivative identity plus explicit tail. |
| EV-054 | Uniform `[a,b]` mean is `(a+b)/2`. | A | Prop. 11.5, exact polynomial quadrature/symmetry. |
| EV-055 | Exponential mean is `1/lambda`. | A | Prop. 11.6, finite integration by parts and exponential tail. |
| EV-056 | Normal `N(mu,sigma^2)` mean is `mu`. | A | Prop. 11.7, oddness after translation and an effective Gaussian tail. |
| EV-057 | Standard normal mean is zero. | A | Special case of Prop. 11.7. |
| EV-058 | Pareto mean is `alpha k/(alpha-1)` for `alpha>1`. | A | Prop. 11.8, with integer/rational parameter code and regular powers. |
| EV-059 | Pareto mean is infinite for `0<alpha<=1`. | A | Prop. 11.8, explicit logarithmic/power divergence. |
| EV-060 | Cauchy expectation is undefined. | A/C | Prop. 11.9: positive and negative parts diverge logarithmically. |

## Algebraic properties

| ID | Article claim | Status | Constructive result |
|---|---|---:|---|
| EV-070 | Nonnegativity. | E | Thm. 5.1. |
| EV-071 | Additivity and homogeneity. | E | Thm. 5.2. |
| EV-072 | Finite linear-combination formula. | E | Cor. 5.3 by quantifier-free induction on the number of summands. |
| EV-073 | Expectation is a linear form. | E | Cor. 5.4 on the finite rational module of observables. |
| EV-074 | Monotonicity. | E/M | Thm. 5.5 and its effective-L1 lift. |
| EV-075 | `E|X|=0` implies `X=0` almost surely. | E | Thm. 5.10 using zero-sum elimination on nonnegative natural weights. |
| EV-076 | Almost-sure equality preserves expectation. | E/M | Thm. 5.11; effective analogue uses zero L1 distance. |
| EV-077 | Expectation of a constant is the constant. | E | Cor. 5.6. |
| EV-078 | `E[E[X]]=E[X]`. | E | Cor. 5.6. |
| EV-079 | `|E[X]| <= E|X|`. | E/M | Thm. 5.9 by monotonicity and the positive/negative-part decomposition. |
| EV-080 | Indicator expectation is event probability. | E | Thm. 5.12. |
| EV-081 | Discrete LOTUS. | E | Thm. 3.7 by finite fiber regrouping. |
| EV-082 | Multidimensional LOTUS. | E/M | Cor. 3.8 and effective quadrature lift. |
| EV-083 | Expectation is not multiplicative in general. | C | Ex. 7.4: `X=Y` on a symmetric sign law gives `E[XY]=1` but `E[X]E[Y]=0`. |
| EV-084 | Independence implies `E[XY]=E[X]E[Y]`. | E/M | Thm. 7.2; finite product weights and effective Fubini lift. |
| EV-085 | Dependent variables may still satisfy the product equality. | C | Ex. 7.5: uniform `X in {-1,0,1}`, `Y=X^2`. |

## Inequalities

| ID | Article claim | Status | Constructive result |
|---|---|---:|---|
| EV-090 | Markov inequality. | E/M | Thm. 6.1 from `a 1_{X>=a} <= X`. |
| EV-091 | Chebyshev inequality. | E/M | Thm. 6.3 by Markov on the squared centered variable. |
| EV-092 | At least 75% within two standard deviations. | E | Cor. 6.4 in variance-scaled, division-free form. |
| EV-093 | Die/Chebyshev `53%` illustration. | C/E | Audit 4.5: `8/15` is the Chebyshev lower bound for the open interval `(1,6)`; its exact probability is `2/3`, while the inclusive event `[1,6]` has probability one. |
| EV-094 | Jensen inequality. | E/M | Thm. 6.6 for finite supporting-line certificates; the effective lift follows from Thm. 10.4. |
| EV-095 | Lyapunov moment inequality. | M/A | Cor. 6.14 in power-cleared/effective rational-exponent form, with primitive-recursive root bisection. |
| EV-096 | Holder inequality. | E/M | Exact Cauchy--Schwarz Thm. 6.11; general rational-conjugate effective form Thm. 6.13. |
| EV-097 | Minkowski inequality. | E/M | Exact `p=1,2`; effective rational-exponent theorem Thm. 6.15. |

## Convergence and countable additivity

| ID | Article claim | Status | Constructive result |
|---|---|---:|---|
| EV-100 | Pointwise convergence need not imply convergence of expectations. | C | Ex. 12.1: dyadic atomic spike sequence with `E[X_n]=1` and pointwise limit zero. |
| EV-101 | Expectation is not countably additive for arbitrary signed sequences. | C | Ex. 12.2: telescoping spike differences sum pointwise to zero while expectations sum to one. |
| EV-102 | Monotone convergence for nonnegative variables. | M | Thm. 12.3 with an explicit expectation-tail modulus; without it only the lower-real form is claimed. |
| EV-103 | Countable additivity for nonnegative variables. | M | Cor. 12.4 from finite additivity plus a tail modulus/lower-real reading. |
| EV-104 | Fatou's lemma. | E/M | Finite Fatou kernel Lem. 12.5 and effective liminf Thm. 12.6. |
| EV-105 | Fatou corollary under a uniform expectation bound. | M | Immediate consequence of Thm. 12.6 by bounding the numerical liminf. |
| EV-106 | Dominated convergence. | M | Thm. 12.9 under an explicit convergence-in-probability and domination/tail certificate. |
| EV-107 | `E|X| <= E[Y]` under domination. | M | A direct consequence of the domination hypothesis in Thm. 12.9 and monotonicity. |
| EV-108 | `E[X_n] -> E[X]`. | M | Final conclusion of Thm. 12.9. |
| EV-109 | `E|X_n-X| -> 0`. | M | Main quantitative conclusion of Thm. 12.9. |
| EV-110 | Uniform integrability can justify interchange. | M | Thm. 12.11. |

## Characteristic functions

| ID | Article claim | Status | Constructive result |
|---|---|---:|---|
| EV-120 | Characteristic function is expectation of `exp(itX)`. | M/A | Sec. 13.1 using regular sine/cosine names. |
| EV-121 | The first derivative at zero recovers the mean. | M/A | Thm. 13.1 with explicit remainder `<= |h| E[X^2]/2`. |
| EV-122 | Fourier inversion recovers a density/mass function. | E/M | Thm. 13.2 gives exact finite cyclic inversion; Thm. 13.3 states the effective continuous version with Fubini/integrability moduli. |
| EV-123 | `E[g(X)]` can be expressed through Fourier transforms. | E/M | Thm. 13.2 on a finite cyclic group; effective integral analogue in Thm. 13.3. |

## Uses and applications

| ID | Article claim | Status | Constructive result |
|---|---|---:|---|
| EV-130 | Sample mean is unbiased. | E | Thm. 8.1. |
| EV-131 | Sample mean minimizes sum of squared residuals. | E | Thm. 8.3, exact completed-square identity. |
| EV-132 | Variance of sample mean decreases with sample size. | E | Thm. 8.2: `Var(bar X)=Var(X)/n` under finite independence. |
| EV-133 | Probabilities can be estimated by indicator frequencies. | E/M | Thm. 13.9 identifies probabilities with indicator expectations; Thm. 8.4 gives the Chebyshev frequency bound. |
| EV-134 | Monte Carlo quantities are expectations. | E/M | Sec. 13.6 and Thm. 13.9: exact finite estimator and error certificate. |
| EV-135 | Powers give moments; centered powers give central moments. | E | Def. 13.4. |
| EV-136 | Moments can determine some distributions. | E | Thm. 13.5: bounded integer support is determined by moments through degree `B`. |
| EV-137 | Center of mass balances at the expectation. | E | Thm. 13.10: zero first moment about the mean and uniqueness. |
| EV-138 | Variance formula `E[X^2]-(E[X])^2`. | E/M | Thm. 5.18. |
| EV-139 | Finite decision makers may maximize expected utility. | E | Thm. 13.7: primitive-recursive bounded search over a finite action set. |
| EV-140 | Quantum expectation and variance formulas. | E/M | Thm. 13.13 for finite-dimensional rational/algebraic Hermitian data. |
| EV-141 | Law of total expectation (listed under see also). | E/M | Thm. 7.8 for finite partitions and effective limit lift. |

## Not treated as proof obligations

History, etymology, and notation claims are classified **H**.  The manuscript
records them only as source context.  The full classical equivalence of all
measure-theoretic absolute-continuity formulations and unqualified versions of
Radon--Nikodym, Fubini--Tonelli, or dominated convergence are classified **R**:
they become iPRA statements only after data, codes, and effective moduli are
made explicit.
