# Report147: exact Python companion

Python 3.10+; standard library only. No installation, network, floating-point
arithmetic, symbolic algebra package, or special-function dependency is needed.
All integer and rational expectations are typed fixtures, not decimal stand-ins.

## Replay

Run from this directory:

```sh
python -m unittest discover -s tests -v
python -O -m unittest discover -s tests -v
python certificate.py > replay.json
python -O certificate.py > replay_optimized.json
cmp certificate.json replay.json
cmp replay.json replay_optimized.json
```

Both test runs contain **56 tests**. The saved `certificate.json` is generated
with the default `--max-n 24`. Exact JSON is deterministic, with rational values
encoded as `{ "numerator": integer, "denominator": positive_integer }`.
No timestamps, host names, timings, floats, or interpreter flags enter it.
`status: PASS` is emitted only after all certificate checks succeed. Failures
raise explicit exceptions and exit nonzero; checks survive `python -O`.

For an explicitly named **new** file, use:

```sh
python certificate.py --output replay_new.json
```

The `--output` option refuses existing paths, symlink components, `..` traversal,
and paths outside this directory. Its parent directory must already exist.
A larger finite coefficient check is available with `--max-n N` (`N >= 11`);
its certificate intentionally differs from the default. Cost increases with N.
The default checks finish quickly on an ordinary Python interpreter.

## What is checked

- Both twelve-term OEIS prefixes, including index zero, use hard-coded integer
  fixtures. Three independently structured engines agree on **every coefficient
  of every row** with outer exponent n and degree n, for n=0,...,24:
  Euler recurrence, direct binomial product, and isolated-core logarithmic atom
  multiplication. Tests additionally check independent exponent/degree pairs.
- A literal unpruned implementation of the finite defect-profile identity is
  checked through n=9 in the certificate, and through n=10 in the tests.
- Exhaustive inclusive phase cutoffs use only the rational sixth-power bound
  `mu^6 <= 9^r (8/9)^D`. Each residue gets its own minimal exclusive degree
  bound and complete eligible-atom list. Recursion prunes only when a necessary
  exact degree or decreasing loss-product condition fails. Small cases are
  cross-checked against a separate, unpruned enumeration.
- All **18 common displayed phases** are checked, with profile counts
  **14,21,17**, bounds **D<19,23,21**, and equality of both signs. The complete
  contributing profiles and rational coefficients appear in the JSON.
- The first differences have **3,2,1** odd profiles, bounds **D<42,40,38**, and
  aggregate A/Z coefficients `(5/2)(m)_2`, `2m`, `1`. The A/L coefficients are
  also checked explicitly. The per-residue atom lists are finer than their union.
- Exact inverse ingredients include Bernoulli polynomials, shifted-Stirling
  coefficients, adjacent leading-model ratios, and `(8/9)^2 = 64/81`. The
  independent safe uniform-tail onset n=192 is checked by a rational sixth-power
  inequality; it is **not** an operational onset for the integer inverse theorem.
- Crossover checks include independent exact constructions of H coefficients,
  all three residue-series prefixes, symbolic Q/E polynomial identities,
  finite P-factor coefficients, and cleared-denominator inequalities proving
  `2 < delta < 3` and `eta > 3`.
- Invalid signs, types (including bool and float), residues, degrees, cutoffs,
  profile ordering/multiplicities, malformed CLI arguments, and unsafe output
  paths are rejected. A deliberate failing check is tested under `python -O`.

## API

In `diagonal_euler.py`:

- `euler_row(exponent, degree, epsilon)`
- `direct_product_row(exponent, degree, epsilon)`
- `logarithmic_atom_row(exponent, degree, epsilon)`

These return tuples through the requested degree. The **outer exponent is fixed
for the entire row**, independently of coefficient degree. Both arguments must
be nonnegative integers and epsilon must be +1 or -1. `diagonal(n, epsilon,
method="euler")` is the exponent=degree=n specialization. Additional exact APIs
are `enumerate_sectors(residue, absolute_floor, odd_only=False)`,
`grouped_terms(...)`, `profile_identity(n, epsilon)`, `leading_model(n)`,
`bernoulli_polynomial(order, x)`, and `shifted_stirling_coefficient(residue, k)`.
The leading residue-one factorial model is not defined at n=1 and rejects it.

In `crossover.py`, `h_coefficient(k)` uses the factorial sum and
`h_coefficients(order)` uses its independent differential recurrence.
`psi_coefficients(residue, order)`, `p_factor(m, ell)`,
`p_inverse_m_polynomial(ell)`, `derived_q_e_polynomials(residue)`, and
`rational_exponent_inequalities()` expose the exact supplement checks.
Polynomial coefficient tuples are in ascending power order.

## Files and interpretation

`fixtures.py` contains semantic expectations transcribed from Report147 and its
exact sector tables. The source SHA-256 in `certificate.py` identifies the
delivered `Report147.tex`; the JSON also records the public OEIS source URLs.
Replay is self-contained and does not read any external source files.
`tests/test_exact.py` and `tests/test_crossover.py` are the test suite.

The sector term convention is **A/Z**, written
`coefficient * (m)_falling_degree * mu^n`, with
`relative_phase = mu / leading_phase`. Thus residue one's leading coefficient
is `(3/2)m`; dividing it out produces the A/L coefficients. In particular, its
relative phase 3/4 has A/Z coefficient 1 and A/L coefficient `2/(3m)`.

This companion certifies exact finite arithmetic and identities. It does not
turn finite tests into a proof of a limit, analytic convergence, or uniform
asymptotic error. Those claims require the report's proofs. No real-parameter
numerical special functions, validated interval inverse, arbitrary finite-X
threshold certificate, or optimized inverse onset is supplied.
