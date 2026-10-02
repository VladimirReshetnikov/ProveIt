# Reproducing the coefficient and inverse checks

Run these commands from the report's top-level directory. Python 3.11 or newer
is required. No network access, external sequence files, or symbolic-algebra
package is needed for the main verifier.

```sh
python3 scripts/verify.py
```

The default run computes every `a_n`, `d_n`, and `c_n` for `0 <= n <= 500` using
exact Python integers. It checks:

- `D` against its independent differential recurrence at every index through 500
- `D` and `H=2D^3` against their literal binomial expansions through degree 40
- The `c` transform by inverse signed Stirling transformation through index 500
- Six correction polynomials against an independent rational power-series
  calculation, all 24 displayed A229741 terms and all 21 displayed A260879 terms
  in the official-entry snapshots read on 2 October 2026
- Numerical ratios at indices 20, 50, 100, 200, 350, 500 using 80-digit Decimal
  arithmetic, with a repeat at 100 digits to check every displayed value

The literal binomial check is cubic in its requested depth; the coefficient
recurrences and the differential check use quadratically many integer operations.
Increase depths explicitly if desired:

```sh
python3 scripts/verify.py --max-index 1000 --binomial-order 60 --points 100 300 600 1000
```

## Optional smooth-inverse checks

Only this step needs the pinned `mpmath` dependency:

```sh
python3 -m pip install -r requirements.txt
python3 scripts/inverse_checks.py
```

This computes exact `c_k` internally through index 1000. At indices 100, 300,
600, and 1000 it checks the Lambert seed, the first explicit shift, and selected
Gamma-model inverses with correction orders 0, 1, 3, and 6. Newton iteration uses
an explicit digamma derivative and a stringent residual test. Displayed values
are repeated at 20 extra working decimal digits. Numerical stabilization is
not an interval-arithmetic proof.

The same run separately checks the original sequence at `y=a_n`, using the
model `B_J(x)=Gamma(x+1)*P_J(1/x)` with `P_J(t)=sum_{j=0}^J c_j*t^j`, orders
0, 3, and 6, and the same four indices. Its Lambert seed is
`u0=Y/W(Y/e)`; the first shift is
`-(log(u0)+log(2*pi))/(2*(1+W(Y/e)))`.

## Generated files

By default all outputs go in the top-level `results/` directory, independently
of the current working directory. Every script accepts `--output-dir`; run
`--help` for the other options. Outputs do not include timestamps or absolute
paths, so identical inputs and the pinned dependency yield byte-stable files.

- `exact_coefficients.csv`: every exact integer coefficient from the main run
- `corrections.json`: exact `h_0,...,h_6` and polynomial coefficient vectors in
  ascending powers of `rho`, with entry zero representing the constant 1
- `verification.json`: check depths, precisions, and success status
- `normalized_ratios.json` and `.csv`: normalized ratios and residuals after
  orders 1, 3, and 6
- `inverse_checks.json` and `.csv`: optional smooth-inverse results
- `original_inverse_checks.json` and `.csv`: optional original-sequence
  smooth-inverse results (not included in the compact article tables)
- `numerical_tables.tex`: compact LaTeX tables generated from those JSON files

Both calculation scripts regenerate the table file. To regenerate only tables:

```sh
python3 scripts/render_tables.py
```

Table generation includes available data in the chosen output directory. For a
fresh isolated run, use an empty directory; older optional inverse data are
otherwise preserved when running only `verify.py`.

The inverse model is explicitly
`F_J(x)=Gamma(x)*rho^(-x)*Q_J(1/(x-1))`, with `rho=log(2)` and `y=c_k`.
It is not a canonical interpolation of the integer sequence. These programs
illustrate fixed-order asymptotics and verify exact finite algebra; they do not
certify asymptotic remainder constants, optimal truncation, Borel continuation,
or rounded integer thresholds.

## Factorial half-truncation remainder checks

Run these standard-library scripts in this order:

```sh
python3 scripts/remainder_coefficients.py
python3 scripts/remainder_checks.py
```

Both accept `--output-dir`. The first generates exact even/odd scalar coefficients through order nine in `scalar-coefficients.json`. The second reads that file, independently verifies the positive complement and finite shape identities for n=2,...,64, and computes exact integer remainders through n=1001. Decimal arithmetic is used only to print exact rational ratios and model residuals in `remainder-checks.json`. These are checks of the factorial-basis cutoff j<n/2, not the least-term inverse-power cutoff.
