# Verification notes

The article supplies the proofs. These scripts check finite symbolic
calculations and independently compare analytic representations. They
do not formalize normal convergence or analytic continuation, and they
do not use interval arithmetic.

## Exact harmonic work

```sh
python3 harmonic_power_reduce.py 5 --output power5.json
python3 verify_harmonic_powers.py --output exact_checks.json
```

The compiler accepts any fixed positive integer power. Its finite
quasi-shuffle reduction has no hard-coded maximum power, although the
symbolic work grows rapidly. The verifier checks sixty exact finite
identities, including the printed fifth finite harmonic sum and moving-order
identities on finite lattices through power six. The classical low-weight
MZV table is an explicitly stated mathematical input; it is not proved
by this test suite.

## Independent numerical comparisons

Run these from this directory:

```sh
python3 check_mixed_orientation.py
python3 verify_multiple_resolvents.py --output multiple_resolvents.json
python3 check_mixed_log.py
python3 verify_special_mixed_log.py
python3 verify_collision_kernels.py
python3 verify_fifth_numeric.py --output numeric_fifth.json
python3 verify_higher_collision.py
```

The root-level `run_checks.py --all` runs this entire sequence and writes
individual replay logs plus `replay_summary.json`.

| Script | Independent representations and scope |
|---|---|
| `check_mixed_orientation.py` | Ten exact residue/logarithm checks; ordinary beta quadrature; four transverse rays and three curved exponent paths. |
| `verify_multiple_resolvents.py` | Three distinct complex resolvents, two orientations, five Fourier modes; Gamma convolution through indices 160 versus direct cotangent-branch quadrature; finite-spectrum exponential and log-Gamma transforms. |
| `check_mixed_log.py` | Direct Bernoulli-weighted logarithmic integrals versus finite nested polylogarithmic sums, at three disk-coordinate pairs. |
| `verify_special_mixed_log.py` | Direct coordinate finite part versus a separately subtracted Mellin representation of the harmonic Laurent coefficient eta. |
| `verify_collision_kernels.py` | Eight direct dilogarithm-kernel quadratures, three exact all-pole coefficients, and three exact finite anomalies. |
| `verify_fifth_numeric.py` | Local Taylor-series integration plus ordinary quadrature versus the convergent polygamma series with a truncated asymptotic tail. |
| `verify_higher_collision.py` | Fifteen direct circle finite parts, with singularities subtracted independently of the proposed collision counterterms; a separate merged integral and Taylor-evaluator checks. |

## Interpreting the data

The JSON files record inputs, precision, methods, and observed residuals.
Working precision is not an error bound. An observed zero residual can
mean that the difference rounded to zero at that working precision.
The fifth-power comparison agrees to forty-eight decimal places, with
observed difference about `3.394e-49`, despite using seventy working digits.

For the geometric limits, `C_minus_T_minus_Q` is the actual remainder at a
positive separation. It tends to zero; it is not an equality error that
must be tiny at every tested separation. The theorem for arbitrary
hierarchical gaps is established by the fixed-contour Hermite proof and
its uniform integrable majorant, not by those fifteen sampled quadratures.

All raw records are retained so another implementation can compare the
same conventions. The coordinate finite parts, strict harmonic ordering,
branches, and Laurent-coefficient signs are defined in the article.
