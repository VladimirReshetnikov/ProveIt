# Exploratory factored-radix companion

This directory preserves one final semantic experiment and its five exact
integral projections. It does **not** improve the variable/degree frontier
reported in the main release. The construction factors the self-radix power
as (q=N P), with (N=B^x) and (P=H^x), and changes the size frame to a
sum of 35 explicit squares. The proof explains why the weaker bound on the
two composite bases still suffices for the inherited power argument.

| Endpoint | Unrestricted integer variables | Residuals | Polynomial degree | Expanded terms | Height |
| --- | ---: | ---: | ---: | ---: | ---: |
| `factored_radix224/equation.json` | 224 | 161 | 6 | 9,936 | 128,846 |
| `factored_radical219/equation.json` | 219 | 156 | 6 | 9,905 | 45,361 |

In each case the polynomial is the sum of the squares of all listed
residuals. The residual degree is exactly three. These intermediate
equations are retained for their distinct frame argument and reproducible
algebra; no optimality or new frontier point is claimed.

## Contents and evidence

- `FACTORED_RADIX_PROOF.md` gives the mathematical semantic argument and
  identifies its inherited C222/ZF/ZFC calibration boundary.
- `factored_radix224/` contains the exact polynomial data, its expansion,
  numerical metrics, and a description of the semantic change from
  `../../sources/p225.json` (relative to this directory).
- `factored_radical219/` contains the final equation and a self-contained
  certificate for five integral shears, unit-pivot projections, and 38
  elementary row operations. All certificate indices refer to the
  currently transformed equation at that step.
- `check_factored_radix.py` independently reconstructs the changed frame,
  audits every requested index and output, compares every residual and
  variable descriptor, and expands the sum of squares.
- `replay_factored_radical.py` independently replays the certificate,
  reverses every shear, checks all unit restorations, reverses the row
  operations, and compares the complete 219-variable endpoint, including
  metadata. It also checks that all 219 coordinates occur.

Both checkers use only the Python standard library. They import no
constructor, no other checker, and no source archive. Their default paths
are relative to their own files, so they run from any current directory.
The finite checks certify the supplied algebraic data. They do not replace
the unbounded mathematical proof or its inherited logical calibration.

## Reproduce the checks

From the release root, run:

```sh
python research/factored_radix/check_factored_radix.py
python research/factored_radix/replay_factored_radical.py
python -O research/factored_radix/check_factored_radix.py
python -O research/factored_radix/replay_factored_radical.py
```

The `--receipt PATH` option writes a detailed JSON receipt. The checked-in
normal and optimized receipts are `FACTORED_RADIX_CHECK.json`,
`FACTORED_RADIX_CHECK_OPTIMIZED.json`, `FACTORED_RADICAL_CHECK.json`, and
`FACTORED_RADICAL_CHECK_OPTIMIZED.json`; each pair is identical. `CHECKS.json`
records the executions and confirms their agreement. Explicit exceptions
keep every check active under Python's optimization flag.

The radix checker rejects a deliberately changed endpoint coefficient.
The radical checker separately rejects a changed shear coefficient, a
changed unit-pivot restoration, a changed row-operation coefficient, and
a changed endpoint coefficient. The receipts include the rejection reasons
and exact hashes of the input data. Superseded split-radix and greedy
experiments are omitted from this release directory.
