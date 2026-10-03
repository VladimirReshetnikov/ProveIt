# Numerical replay

Python 3.10 or later and mpmath 1.3.0 are required. Install the pinned dependency
with `python3 -m pip install -r code/requirements.txt` if needed. The calculation
itself is offline and uses no absolute source-workspace paths.

From the bundle root:

```sh
bash code/reproduce.sh
```

The runner generates fresh files under `replay-output/`, verifies all integer
counts through 400 by two independently implemented recurrences, compares three
Puiseux/Gamma runs (two nested-input routes) against the bundled reference data,
and checks specified-model Lambert and purely logarithmic inverse generators.
It reports failures with a nonzero exit code. Select another output directory
with `bash code/reproduce.sh --output-dir /desired/output/directory`.
Set `PYTHON=/path/to/python` to use a particular interpreter. The files work
after extraction at a different path and do not require executable permission.

## Individual generators

```sh
python3 code/check_identity.py --degrees 2 3 4 --N 400 --output counts.json
python3 code/identity_allorders.py --degrees 3 4 --N 400 --precision 110 --order 4 --route sum --output jets.json
python3 code/identity_allorders.py --degrees 3 --N 250 --precision 80 --order 4 --route differentiate --output jets-taylor.json
python3 code/identity_inverse.py --input jets.json --model-order 4 --inverse-order 4 --output inverse.json
python3 code/identity_inverse.py --input jets.json --model-order 2 --inverse-order 6 --output inverse-finite-model.json
```

The count generator uses only the Python standard library. The all-order
generator uses cached exact counts when available and enumerates them otherwise.
`--N` controls the nested-input truncation, not a certified error bound. Counts
in the cache are verified independently by the replay runner. `--order` is any
fixed nonnegative order; computational cost and precision needs grow with it.
The root solve checks the expected characteristic signs; arbitrary degrees or
orders may need greater truncation/precision and are not certified by this run.

`--model-order R` fixes the exact finite smooth model Q_R. The separate
`--inverse-order K` controls the number of generated inverse correction terms.
The implementation explicitly sets D_j=0 for j>R even if higher correction
coefficients are present in the input. For K>R these are coefficients of that
finite model, not the inverse of an unspecified continuation of the full series.
An R=0 model has identically zero Lambert-correction coefficients.

## Sign and data conventions

- Count residuals are `exact_count / truncated_asymptotic - 1` (signed)
- Inverse residuals are `approximate_inverse - model_inverse` or
  `approximate_inverse - exact_n`, as identified by their JSON keys
- `model_inverse_minus_exact_n` separates model error from inverse-series error
- Pure-log polynomial arrays are coefficients in ascending powers of h
- Counts use a zero at array index 0, so array index equals vertex count
- Decimal strings preserve the working precision; they are not interval bounds

`data/identity-checks.json` contains counts through n=400 (d=2,3,4) and an
initial 60-digit characteristic calculation. `data/identity-allorders-checks.json`
contains the original 70-, 110-, and 80-digit runs. The independently generated
replay outputs include explicit residual signs and additional checks.
`data/identity-inverse-checks.json` is the original R=K=4 inverse reference;
the fresh inverse output adds all-order pure-log coefficients and tests.
Those fresh R=K=4 outputs are also supplied as
`data/identity-inverse-replay-checks.json`; the R=2/K=6 and R=0/K=4 model tests
are supplied as `data/identity-inverse-extended-checks.json`.

The 1e-60 agreement test is a numerical stability test. It is neither an
interval-arithmetic proof of decimal digits nor an unconditional exact-ceiling
rule for an integer threshold.
