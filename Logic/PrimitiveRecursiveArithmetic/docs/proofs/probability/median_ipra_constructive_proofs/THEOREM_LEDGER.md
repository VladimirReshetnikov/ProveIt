# Median article theorem ledger

Prepared 2026-11-16 against the current English Wikipedia article `Median`.

## Status codes

- **A** - fully proved in the manuscript by a finite, division-free argument;
  the proof is organized for primitive-recursive definitions and
  quantifier-free induction in iPRA.
- **B** - fully proved as an effective theorem schema, conditional on explicit
  primitive-recursive regular-name/modulus data.
- **C** - a substantial constructive route is given, but a large imported
  theorem or analytic module remains to be formalized.
- **X** - the article wording needs a restriction or correction; a finite
  counterexample or corrected theorem is supplied.

No status asserts that the accompanying Lean blueprints already compile or
that a `Prf PRAAx` term has already been constructed.

| # | Article statement or topic | Status | Result in this packet |
|---:|---|:---:|---|
| 1 | Odd sample median is the middle ordered value | A | The middle-interval theorem gives the unique median `x_q` for length `2q+1`. |
| 2 | Even conventional median is the mean of the two middle values | A | All balance medians form `[x_{q-1},x_q]`; the conventional choice has doubled value `x_{q-1}+x_q`. |
| 3 | At least half lie on each side | A | Equivalent to `2 count(<t)<=n` and `2 count(>t)<=n`. |
| 4 | Existence of a finite median | A | Insertion sort is primitive recursive; either middle endpoint is a witness. |
| 5 | Nonuniqueness | A | The complete median set is exactly the closed middle interval. |
| 6 | Uniqueness | A | Unique exactly when the two middle order statistics agree; always unique for odd length. |
| 7 | Median needs only an order, not a metric | A | The proof uses comparisons only. Finite ordinal grades can replace numerical data. |
| 8 | Median as quartile/decile/percentile | A | The half-count predicate is exactly the lower/upper 1/2-quantile predicate; hence Q2, D5, P50. |
| 9 | Insensitivity to extreme observations | A | Rank envelopes show that changes outside the central ranks do not move the median until they cross a middle rank. |
| 10 | Robustness to replacements | A | If at most `r` entries change, interior order statistics move by at most `r` ranks. |
| 11 | Replacement breakdown point | A | The conventional sample median has finite-sample replacement breakdown `ceil(n/2)/n`. |
| 12 | Probability median definition | A | Exact for finite weighted rational laws after clearing the common denominator. |
| 13 | CDF characterization | A | `F(m-)<=1/2<=F(m)` is the same pair of integer mass inequalities. |
| 14 | Existence for finite laws | A | Bounded search for the first cumulative mass at least half produces a median. |
| 15 | Interval of distribution medians | A | Weighted lower and upper half-quantiles are the endpoints. |
| 16 | Arbitrary real distributions have medians | B | Effective version for regular CDF names with tail and locatedness moduli; not qualitative choice over arbitrary reals. |
| 17 | Symmetric distribution has center as median | A/B | A for finite weighted laws; B for effectively presented continuous laws. |
| 18 | Symmetric distribution mean equals center | A/B | A for finite laws by pair cancellation; B when an effective integrability modulus is supplied. |
| 19 | Symmetric unimodal median equals mode | A/B | On a consecutive symmetric grid, the center is a median and the central grid point(s) lie in the mode plateau; a unique mode must be the symmetry center. |
| 20 | Normal median | B | Follows from symmetry of the regular normal CDF. |
| 21 | Uniform median `(a+b)/2` | A/B | A for finite arithmetic grids; B for a regular uniform law. |
| 22 | Cauchy median | B | Follows from symmetry; no mean is needed. |
| 23 | Exponential median `ln(2)/lambda` | B | Solve the regular-name equation `exp(-lambda m)=1/2`. |
| 24 | Weibull median | B | Solve `exp(-(m/lambda)^k)=1/2`. |
| 25 | Power-law median | B | Solve the tail equation `(xmin/m)^(a-1)=1/2`. |
| 26 | Median minimizes mean absolute error | A | Pairing proof for samples; repeated-weight proof for finite laws. |
| 27 | Complete set of L1 minimizers | A | Exactly the middle interval, not merely the conventional midpoint. |
| 28 | Mean-median distance at most one standard deviation | A | Proved in denominator-cleared form `(2S-MW)^2 <= 4(WQ-S^2)`. |
| 29 | Multivariate norm version | B | Finite proof schema using a regular norm and spatial L1 minimizer. |
| 30 | Sharper `sqrt(3/5)` unimodal bound | X/C | The unrestricted discrete reading is false: weights `(2,3)` at `(0,1)` give ratio squared `2/3>3/5`. Continuous hypotheses need a separate Gauss-inequality module. |
| 31 | Median-mode `sqrt(3)` bound | C | Requires a precise continuous-unimodality theorem and effective tail integration. |
| 32 | Monotone density has mean above median | B | Effective continuous proof can use decreasing-density layer-cake bounds; it is not a theorem for arbitrary discrete unimodal tables. |
| 33 | Positive skew implies mean above median | X | Counterexample `[0,0,1,1,2]`: third central moment `18/125>0`, mean `4/5`, median `1`. |
| 34 | Jensen inequality for medians | A | Finite theorem for a function whose sublevel sets on the ordered sample are intervals; convex functions satisfy the certificate. |
| 35 | Sorting takes comparison `Omega(n log n)` | A | Decision-tree leaf count `2^d>=n!` plus an explicit factorial lower bound. |
| 36 | Selection computes a median in linear time | A/C | Correctness and recurrence are proved; object-level cost traces remain to be implemented. |
| 37 | Median-of-three | A | Explicit compare-swap formula and correctness. |
| 38 | Tukey ninther | A | For nine distinct inputs its rank is always 4, 5, or 6; exhaustive checker records exact counts. |
| 39 | Remedian is one-pass, linear-time, sublinear-memory | A/C | Base-`b` buffering gives `O(n)` work and `O(b log_b n)` stored values; exact PR cost proof is outlined. |
| 40 | Exact odd discrete sample-median PMF | A | Multinomial formula proved from counts below, equal, and above. |
| 41 | Exact sample-median CDF | A | Binomial tail `P(Bin(N,F(t))>=n+1)`. |
| 42 | Continuous sample-median density | B | Derived effectively from finite-interval differences plus a differentiability modulus. |
| 43 | Beta pushforward | B | Polynomial density and beta moments are finite identities once the effective probability integral transform is supplied. |
| 44 | Asymptotic normality | B | Exact binomial law + effective finite CLT + local inverse-CDF modulus. |
| 45 | Asymptotic variance `1/(4N f(m)^2)` | B | Included with the necessary assumptions `f(m)>0` and an explicit local remainder modulus. |
| 46 | Normal-sample median variance and efficiency `2/pi` | B | Corollary of the normal density at its center and the effective asymptotic theorem. |
| 47 | Delete-one jackknife inconsistency | C | Finite jackknife is PR; the asymptotic inconsistency theorem is inventoried but not proved. |
| 48 | Delete-k and bootstrap consistency/rate | C | Requires a separate effective resampling theory. |
| 49 | Hodges-Lehmann estimator | A/B | Walsh-average list is PR; central symmetry forces its median to the symmetry center. Robustness/efficiency are analytic. |
| 50 | Marginal median | A | Coordinatewise median is defined finitely and minimizes total `l1` distance. |
| 51 | Geometric median minimizes Euclidean distances | B | Definition and rational epsilon-minimizer construction via bounded grids and regular square roots. |
| 52 | Geometric median similarity equivariance | B | Objective scales under effective Euclidean similarities. |
| 53 | Geometric median uniqueness in dimension at least two | X | False without non-collinearity: two points have their entire segment as minimizers. Correct theorem: uniqueness if the data are not collinear. |
| 54 | Median in all directions | C | Projection-median condition and subgradient route are specified; full directional formalization remains. |
| 55 | Centerpoint existence | C | Full Helly-style human proof and fixed-dimension rational-certificate route are given. |
| 56 | Conditional median | A | Finite fiberwise construction. |
| 57 | Conditional median is Bayes-optimal for L1 loss | A | Sum the one-dimensional L1 inequalities over conditioning fibers. |
| 58 | Gaussian-noise linearity characterization | C | Deep analytic characterization; not proved. |
| 59 | Interpolated median formula | A | Derived as `m + w(k-i)/(2j)` and shown equivalent to the CDF formula. |
| 60 | Article's 22/33/45 example | A | Exact value `221/66 = 3.34848...`, rounded to `3.35`. |
| 61 | Pseudomedian | A/B | Median of the symmetrized finite law/Walsh averages; exact symmetry and affine equivariance. |
| 62 | Theil-Sen estimator | A | Pairwise slopes are PR; permutation/affine invariance and exact collinear recovery are proved. |
| 63 | Median filter removes salt-and-pepper noise | A | Exact local theorem: fewer than half corruptions in an odd constant window are removed; interval-majority variant also proved. |
| 64 | k-medians clustering | X/A | Correct objective is minimization of within-cluster L1 distance, not maximization of inter-median distance. Assignment/median updates decrease the finite objective. |
| 65 | Median-median line | A | Exact recovery on collinear data and affine equivariance of grouped medians. |
| 66 | Median-unbiased estimators minimize absolute loss | A | Direct weighted-L1 theorem. |
| 67 | Mean-unbiased estimators minimize squared loss | A | Completed-square identity over finite weighted laws. |
| 68 | Invariance under one-to-one transformations | X | Correct for strictly monotone transformations. Arbitrary injections do not preserve order; `0,1,2 -> 0,100,1` is a counterexample. |
| 69 | General qualitative uses and historical statements | - | Not mathematical theorem targets. |
| 70 | Repository PA `TwiceMedian` result | reference | Reused as a design: sorted permutation, odd/even division-free cases, existence and functionality. The new target is an iPRA `Prf PRAAx` derivation. |
