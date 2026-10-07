# Optional symbolic and interval reproductions

The exact standard-library core and PDF/ZIP builder do not import or run these
programs. They preserve the original independent computational methods for
optional reproduction with SymPy 1.14.0 and mpmath 1.3.0. These versions were
checked locally; see requirements.txt. Install them only in an environment of
your choosing. Installing packages is not part of a build.

## Work only on disposable copies

These historical programs have no read-only or --compare command-line mode.
They write JSON beside themselves and can overwrite an existing file with that
name. Never execute them inside the source package or extracted release.
Instead, copy their directories into a fresh temporary directory. For example,
from the package root on a POSIX shell:

```
work=$(mktemp -d)
cp -R optional/producer optional/audit optional/root "$work/"
cp optional/check_length.py "$work/"
python -B "$work/producer/certify_entringer.py"
python -B "$work/producer/check_marked_coefficients.py"
python -B "$work/audit/check_exact.py"
python -B "$work/root/check.py"
python -B "$work/check_length.py"
cmp "$work/producer/entringer_diagnostics.json" data/references/entringer_diagnostics.json
cmp "$work/producer/entringer_connection_certificate.json" data/references/entringer_connection_certificate.json
cmp "$work/producer/marked_coefficients.json" data/references/marked_coefficients.json
cmp "$work/audit/exact_checks.json" data/references/exact_checks.json
cmp "$work/root/checks.json" data/references/checks.json
cmp "$work/length_diagnostics.json" data/references/length_diagnostics.json
```

certify_entringer.py invokes verify_entringer.py first, so both producer scripts
must remain together. Python's -S option must not be used for these optional
runs: they need their installed site packages. The scripts use explicit checks;
an additional python -B -O run can be made on a second fresh copy. Keep the
frozen data unchanged if reproduction differs, and investigate the difference.

All producer and independent-audit scripts are byte-for-byte copies. The root
script has one output-location adaptation: its original fixed absolute JSON
destination is replaced by Path(__file__).with_name('checks.json'), with the
corresponding pathlib import. Its calculation is unchanged. Original and
packaged hashes and this adaptation are recorded in data/PROVENANCE.json.

## What each program establishes

- producer/verify_entringer.py: exact scalar ODE/triangle checks through n=101,
  the 21 visible source terms, symbolic correction generation, 110-digit
  interior connection diagnostics, and finite-N residual experiments. It
  computes exact counts through n=802, but the ODE comparison stops at n=101
- producer/certify_entringer.py: a 90-decimal-place interval evaluation of the
  midpoint Wronskian, using exact rational inputs, an interval for pi, and
  proved tails at M=420. It writes both producer diagnostics and the interval
  certificate
- producer/check_marked_coefficients.py: symbolic low-order marked,
  normalized-PGF, log-PGF, mean, and variance corrections
- audit/check_exact.py: independently constructed marked triangle/ODE
  polynomial identities for n=2,...,18, direct formal Frobenius checks,
  exact P_10 Sturm/root evidence, and diagnostic approximate roots
- check_length.py: independent smooth optical-length quadrature at 50, 100,
  and 150 digits. It supports L approximately 4.2586174557 as a diagnostic;
  no interval accuracy or large-mark remainder constant is certified
- root/check.py: a separate scalar coefficient expansion through inverse
  order six and high-precision amplitude estimates from finite-N data

data/references/finite_nonreal_counterexample.json is an additional frozen
root-check record. Its polynomial and exact Sturm conclusion are independently
checked by the audit script and the standard-library core. There is no separate
bundled generator for that original JSON file.

## Evidence limits

The amplitude enclosure combines an analytic tail proof with conventional
interval arithmetic. Its finite arithmetic relies on mpmath's interval
implementation, which this package does not independently validate. SymPy and
mpmath themselves are not formally verified here. More digits in a diagnostic
string do not imply more certified digits.

Ordinary multiprecision residuals, approximate roots, and stabilization at a few
values of N are diagnostics. They are not interval error bounds, finite-N
remainder constants, proofs of the uniform analytic theorems, or a guarantee of
correct inverse rounding. Exact symbolic checks have only the ranges stated.
Dependency changes can alter expression formatting or numerical strings and
break byte comparisons without changing the underlying mathematical identity.

The optical-length diagnostic accompanies a separate theorem for real lambda
tending to positive infinity. It is not a joint growing-lambda/N result and
does not justify inserting growing marks into a compact-mark N-expansion.
check_length.py is copied byte-for-byte and writes beside itself, so the
same disposable-working-copy rule applies. No other large-mark scripts are
included in this package.
