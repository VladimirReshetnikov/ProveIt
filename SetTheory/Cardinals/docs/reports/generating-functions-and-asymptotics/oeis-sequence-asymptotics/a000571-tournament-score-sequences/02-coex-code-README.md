# Reproducible checks and numerical figures

Run from the archive's main directory:

```bash
python code/verify_and_plot.py
```

The script uses Python 3, NumPy, SciPy, Matplotlib and mpmath. The supplied
`requirements.txt` records the versions in the generating environment
(Python 3.12.14 on Linux). No web access or randomness is used. Default runtime
was approximately six seconds in that environment. Changing `--sizes`,
`--offset-points`, `--component-n` or `--exact-n` regenerates different sizes.
Memory is linear in the largest size; each scalar renewal calculation uses
quadratic arithmetic work. Outputs are written to the adjacent `data/` and
`figures/` directories.

## What is exact

`exact_checks()` uses Python integers. It first evaluates the divisor formula
for `N_n`, the differential recurrence for the total score count `S_n`, and the
strong-block recurrence for `I_n`. It independently enumerates every
nondecreasing integer sequence of length `n` with entries from `0` to `n-1`,
and applies Landau's inequalities. Equality indices determine every block
size and hence both the number of blocks and existence of a block larger
than `n/2`.

The default run examined 125,476 candidate sequences over `1 <= n <= 10`.
It checks all of the following with exact assertions:

* Divisibility in both integer recurrences.
* Agreement of Landau totals with every `S_n` and `I_n`.
* Agreement of every coefficient in the component-count polynomial.
* Agreement of every coefficient in the marked giant-block identity
  `sum_{j>n/2} u I_j [z^(n-j)](1-uI(z))^(-2)`.

For example, at `n=10` the full component-count polynomial has coefficients
`[0,573,433,246,130,55,33,7,8,0,1]` in ascending powers of the block weight.
The giant-block polynomial has coefficients
`[0,573,424,225,84,35,0,0,0,0,0]`.
The totals at weight one are respectively 1,486 and 1,341.

These checks verify the exact identities at small sizes. They do not prove
the asymptotic theorems.

## Constants and floating recurrences

The constants are computed using the analytic divisor-remainder split in
the article. Remainder numerators are formed by exact integer subtraction;
mpmath then evaluates the rational terms and elementary constants at 90
decimal digits. Truncating the remainder series at `M=200` gives rigorous
*series truncation* bounds `2^(-201)` for lambda and `202*2^(-201)` for mu.
The decimal elementary-function evaluations are not outward-rounded
interval calculations. The JSON file expressly separates these two facts.

Normalized auxiliary coefficients are `nu_n=N_n/4^n`. The script uses

```text
n s_n = sum_(j=1)^n nu_j s_(n-j),        s_0=1,
n i_n = nu_n - sum_(j=1)^(n-1) nu_j i_(n-j),
q_n = i_n/p.
```

The second recurrence follows from differentiating `I=1-exp(-A)`. Scaling
before recursing avoids the exponential growth of the integer counts.
The first 200 divisor coefficients use exact integer formulas before
conversion. Above 200, the proper-divisor remainder is below the working
floating precision and is dropped. The normalized central-binomial
contribution is computed multiplicatively.

In the generating environment, `numpy.longdouble` has 63 stored mantissa
bits (64 significant binary digits including the leading bit). Platforms
where this type equals ordinary double will have different diagnostic
roundoff. No universal numerical error bound is asserted. Exact counts
through 200 and the independent convolution recurrence for `I_n` provide
checks against implementation mistakes; their observed relative
differences appear in `verification_summary.json`.

For each `n` and offset `s`, the script computes the implicit leading-balance center

```text
t_n = -2 W_(-1)(-sqrt(d/m)*n^(-1/4)/2),
tau = t_n+s,
r = 1/(1+m*tau/n),
Z(z) = 1/(1-r Q(z)).
```

Its positive recurrence is `Z_0=1`,
`Z_k=r*sum_(j=1)^k q_j Z_(k-j)`. The giant numerator is evaluated by
convolving `Z` with itself and applying the marked-block identity. The
resulting probabilities are deterministic floating evaluations of exact
coefficient formulas, not Monte Carlo estimates or certified intervals.

## Files and interpretation

* `verification_summary.json`: exact assertion summary, constants,
  arithmetic checks and selected finite-size observations.
* `coexistence_diagnostics.csv`: giant probabilities for 33 offsets in
  `[-4,4]` at sizes 512, 2,000 and 8,000. It also records both leading
  coefficient contributions, their ratios to the calculations and the
  relevant component/remainder scales.
* `renewal_mass.csv`: the entire numerically computed mass sequence through
  8,000; `normalized_counts.csv`: selected normalized count diagnostics.
* `component_count_distribution.csv`: the joint distribution of block
  count and the giant-block event for `n=1000`, `s=0`.
* `giant_probability.pdf` and `.png`: finite-size giant probabilities,
  the limiting logistic curve, and the largest-size two-term prediction.
* `component_count_distribution.pdf` and `.png`: the two joint
  block-count distributions. FFT polynomial products compute these
  values; their aggregate is checked against the positive recurrence.
* `phase_profiles.pdf` and `.png`: theoretical Gamma(2,1) and Frechet
  density profiles, rather than numerical distribution estimates.

The Frechet maximum panel illustrates the proved collective-phase
extreme-value limit with scale `(2*d*n/(3*m))^(2/3)`. The curve is a
plot of the theoretical density, not an independent numerical test of
the convergence theorem.

Finite corrections are substantial. At the implicit leading-balance center `s=0`,
the computed giant probabilities are approximately 0.524116, 0.534177
and 0.549825 for sizes 512, 2,000 and 8,000. The limit is 0.5, but these
values are not yet a monotone approach to the limit. At size 8,000 the
giant numerator is approximately 1.73615 times its leading asymptotic
term, while the full partition function is approximately 1.57882 times
the sum of its two leading terms. The displayed curves therefore
illustrate slow finite-size behavior, and should not be described as
close agreement with the limiting logistic law.

The block-count computation at size 1,000 has giant probability
approximately 0.527852. Its conditional means are approximately 148.45
given a giant block and 468.27 given no giant block. The leading scale
predictions are respectively 134.45 and 580.60. Its FFT sums agree with
the independent recurrence to relative discrepancies below `1.4e-15`
(total) and `1.0e-17` (giant); these are cross-checks between floating
algorithms and not rigorous error estimates.
