# Optional diagnostics

These checks are separate from the standard-library verification target.
Run from the source directory, or invoke the scripts by their location from any
working directory. They do not write files unless `--output PATH` is supplied;
normal successful run output is a single JSON object. No network is used.

Dependencies: `mpmath` for the floating checks; `sympy` for the independent exact
coefficient comparison. Install optional dependencies separately if desired.
The JSON records the installed dependency version used for each run.

## Quick checks

```sh
python optional/diagnostics_sympy.py
python optional/replay_oeis.py
python optional/stable_modes.py
```

- `diagnostics_sympy.py` independently expands the defining formal exponential
  and applies Fresnel moments, then compares against the standard-library
  implementation at orders 0 through 4 and modes 1 and 2. Its comparisons are
  exact, but they do not prove an analytic remainder estimate.
- `replay_oeis.py` defaults to the first three OEIS values, evaluated at 55 and
  75 decimal digits. The omitted positive tail is bounded using the exact
  rational function `code/positive_tail.py:tail_bound(n,T)`.
- `stable_modes.py` defaults to log(x)=20,80, modes 1,2, and one, two, and three
  asymptotic terms. Coefficients for every mode and order are imported from
  `code/exact_coefficients.py`, rather than hard-coded first-mode values. It
  compares cutoffs 10 and 12 at 50 decimal digits.

## Full numerical invocations

```sh
python optional/replay_oeis.py --full --precisions 55 75
python optional/stable_modes.py --full
```

The full replay covers all 35 attributed fixture values, n=0,...,34. The full
mode run uses log(x)=20,40,80,120,200,400,800, modes 1,2,3, cutoffs 14 and 16,
and 70 decimal digits. It can take several minutes. Its `--terms` option can
select one through seven terms, including with `--full`. `--full` overrides
the mode, log(x), cutoff, and precision options for the mode script; it only
overrides the prefix count for the replay script.

Custom smaller runs, for example:

```sh
python optional/stable_modes.py --log-x 80 --modes 2 --terms 1 2 3 4 --digits 60
python optional/replay_oeis.py --count 8 --output replay-eight.json
```

`--help` lists the supported parameter ranges. Values outside those ranges are
rejected. Script execution does not use `assert`, and therefore retains its
checks under Python's `-O` option. Exit status 0 means the requested computation
completed (and exact comparisons or floor diagnostics passed, when applicable),
1 means a comparison failed, and 2 means invalid input, a missing dependency,
or an execution error covered by the script's error handler.

## Included recorded runs

The following records were generated on 2026-10-03 with mpmath 1.3.0 and
SymPy 1.14.0. To regenerate the same four files from the source directory:

```sh
python optional/diagnostics_sympy.py --output optional/sympy_check.json
python optional/replay_oeis.py --full --precisions 55 75 --output optional/oeis_replay_full.json
python optional/stable_modes.py --output optional/stable_modes_quick.json
python optional/stable_modes.py --full --output optional/stable_modes_full.json
```

All ten exact coefficient comparisons passed. All 35 recorded OEIS floors
matched at both precisions. Among n=1,...,34 the smallest diagnostic distance
to a target floor boundary was approximately 0.00169001377462648415 at n=17;
the largest exact tail bound was approximately 7.488459129620889e-56.
The quick mode run contains four (log(x),m) pairs, and the full run contains
21. Both cutoff evaluations agreed at the displayed precision in every row.
These outcomes retain the qualifications below.

The three default script invocations also completed under a Python audit hook
that denied filesystem writes. Invalid parameter guards were exercised with
Python's `-O` flag. These are implementation checks, not mathematical claims.

## What these diagnostics do and do not establish

The OEIS fixture contains only the 35 integer terms in the source record's
S/T/U fields, with attribution and access date. It is not a copy of the full
OEIS export. At n=0 the sum is 1 by the constant-term convention.

The replay's truncation-tail bound is exact rational arithmetic. Its finite
sums, floors, and floor margins still use floating arithmetic: agreement at two
precisions is not interval certification. A floating floor after adding that
tail bound has the same limitation. Likewise, completed-line quadrature uses
finite Gaussian cutoffs, and agreement between two cutoffs is a stability
diagnostic, not a rigorous error enclosure. The full mode values include the
subtracted negative ray. Neither numerical script proves the all-orders
theorem, an effective asymptotic onset, or uniformity in growing mode number.
