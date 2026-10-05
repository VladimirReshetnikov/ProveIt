# Optional exact analytic replay

This directory is separate from the standard-library exact combinatorial suite.
Nothing here is called by the root `run_checks.sh`.

The algebraic program requires Python 3.9+ and **SymPy** (tested with 1.14.0).
Use your normal trusted Python package workflow to install SymPy in a separate
virtual environment if it is not already available. No installation is performed
by the scripts. Run from any directory:

```sh
sh /path/to/bounded_ascent_report/checks/analytics/run_analytic_checks.sh
```

This runs all algebraic comparisons normally and under `python -O`, with explicit
exception-based guards in each mode. `PYTHON=/path/to/python3` selects an
interpreter. The programs contain no removable assertion statements. Runtime is
normally seconds for the bundled cases; higher requested orders can be costly.

## Exact coverage

`sector_coefficients.py` implements the report's finite coefficient formula with
SymPy rational functions, exact centered-moment polynomials, finite convolution,
and the Bernoulli/Stirling correction. Its outputs contain no floating-point
approximations. Both the public function and CLI validate integer `m >= 1` and
integer `order >= 0`; the function also rejects booleans and floating-point values.

`check_analytic_coefficients.py` performs explicit exact comparisons with:

- `f_0(y)=1/(1-y)`, `f_1(y)=-y/(1-y)^3`, and
  `f_2(y)=y(1+2y)/(1-y)^5`
- All 12 printed rational coefficients `c[m,j]`, `m=1,2,3`, `j=0,1,2,3`:
  - `m=1`: `1, 0, 0, 0`
  - `m=2`: `1, -31/8, 5437/128, -896281/1024`
  - `m=3`: `1, -43/3, 32791/81, -40869055/2187`
- Agreement of those outputs at orders zero, two, and three on their common range
- `c[m,0]=1` and `c[m,1]=kappa_m` for `m=1,2,3,4,5,8,12`, with the independently
  entered expression
  `kappa_m = 23m/12 + 13/(12m) - m^2(m+1)/2 - ((m+1)/m) H_m`
- 26 explicit invalid-input cases for sector index and truncation order

To print another finite coefficient list:

```sh
python3 checks/analytics/sector_coefficients.py --m 1 2 3 --order 3
```

Here `n` in the asymptotic sector expansion is the multiplicity cap plus one; it
is unrelated to the word-length limit. The sector index `m` and truncation order
are fixed. This replay checks finite algebra and the stated rational values. The
uniform analytic expansion, localization, asymptotic remainders, and cap-inversion
claims require the arguments in the report. The tests do not establish those
analytic conclusions or claim a convergent infinite inverse-cap series.

## Optional numerical sector diagnostics

`diagnostic_sectors.py` additionally requires **mpmath**, independently of SymPy.
It evaluates a positive-integrand formula and reports sector/leading-term ratios,
first-correction diagnostics, and selected comparisons. For example:

```sh
python3 checks/analytics/diagnostic_sectors.py --n 101 201 --m 1 2 3 --dps 50
```

The output records the dependency version and working precision. Numerical
quadrature, special-function evaluations, finite displayed digits, and small
residuals are not interval certificates or proofs. This program is also excluded
from both exact runners. Increasing precision is a diagnostic experiment, not a
rigorous error analysis. No numerical cap threshold or integer-rounding decision
is certified by these scripts.

## Optional continuous cap-inversion diagnostics

`diagnostic_cap_inversion.py` uses mpmath at 85 decimal digits for the fixed real
values `n=20.3,30.7,50.1,100.4` (the script calls this variable `R`). Run:

```sh
python3 checks/analytics/diagnostic_cap_inversion.py
```

It prints an approximate gap, a Lambert-W envelope root, and the estimated shift
relative to its leading correction. The quadrature stops at `100*n`; the script
does not certify the discarded tail or the numerical errors. Its displayed
precision is not a rigorous error guarantee. This is a diagnostic only, is
excluded from both exact runners, and does not certify an integer-cap choice.
