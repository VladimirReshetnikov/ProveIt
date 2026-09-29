# Sharp negative-direction summability for countable exponential feedback

## Article

**A coefficient-to-remainder principle, optimal logarithmic scales, and sectorial inversion.**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.
The package contains a self-contained 19-page mathematical article, its LaTeX
source, executable checks, recorded results, and provenance notes.

The model is

    U(q) = sum_{j >= 1} q^j exp(lambda_j U(q)),   lambda_j >= 0.

The original formal series need not converge at any nonzero q. The article
constructs the canonical actual solution on proper sectors about the negative
real axis, with U(q) = q + O(q^2).

## Main results

1. Under the explicit admissible-weight hypotheses in Section 2, formal
   coefficient membership in a weight class is equivalent to a uniform,
   all-orders remainder estimate for the canonical sectorial solution.
   The proof uses U = q V, an exact kernel Taylor-remainder inequality, and a
   positive subfamily of the Lagrange coefficients.
2. For every s > 0, strong Gevrey-s asymptotics are equivalent to
   lambda_j = O((j log(j+1))^(s+1)). For every k > 1, negative-direction
   k-summability is equivalent to lambda_j = O((j log(j+1))^(1+1/k)).
3. For slopes comparable to j^p (log(e+j))^beta, p > 1, the optimal
   factorial-logarithmic weight, up to geometric factors, is
   M_n = (n!)^(p-1) product_{l=1}^n (log(e+l))^(beta-p).
   Actual optimally chosen Taylor truncations have error bounded by
   C exp[-c |q|^(-1/(p-1)) (log(1/|q|))^((p-beta)/(p-1))].
4. These strong regularity and summability conclusions extend to the actual
   sectorial compositional inverse. Finite-action fixed-point evaluation has
   an explicit analytic truncation-plus-iteration error bound.

The constants depend on the proper sector and weight data. No uniform
estimate up to the imaginary boundary rays is claimed. In particular,
ordinary negative-direction Borel summability of the quadratic model remains
open in this article. Optimal weight-class order does not mean a sharp
pointwise lower remainder bound or a sharp numerical exponential constant.

## Contents

- `article.tex`, `article.pdf`: self-contained source and compiled article.
- `code/verify.py`: exact coefficient recurrences and independent checks;
  optional high-precision, non-interval numerical diagnostics.
- `data/*_coefficients.csv`: four exact coefficient tables through degree 120.
- `data/sectorial_diagnostics.csv`: finite-action and kernel diagnostics.
- `data/verification.json`, `data/run_output.txt`: executed-run reports.
- `PROOF_STATUS.md`: precise proof dependencies and limitations.
- `SOURCES.md`: pinned repository snapshot and primary literature.
- `requirements.txt`, `Makefile`: reproduction aids.

## Reproduce

The exact checks use only the Python standard library. Python 3.10 or later
is required; the recorded run used Python 3.13.5 and mpmath 1.3.0.

```sh
python code/verify.py --order 120 --exact-only
python -m pip install -r requirements.txt
python code/verify.py --order 120
```

A run replaces the JSON report; `--exact-only` omits the numerical section.
The full run restores it. To record terminal output as supplied here:

```sh
python code/verify.py --order 120 > data/run_output.txt
```

A standard TeX Live installation with the packages listed in the preamble is
sufficient. The source has no external notation, figure, or bibliography files.

```sh
make pdf
```

Or run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` three times.

## What was checked

All **768 exact comparisons** passed: 48 independent partition-formula checks,
480 positive-subfamily inequalities, and 240 zero/linear benchmark checks.
The full run additionally passed 48 high-precision kernel-remainder checks
and six finite-action solver comparisons at 100 decimal digits.

The CSV column `n_factorial_times_u_n` is **n! times the ordinary coefficient**.
The numerator and denominator columns give the ordinary coefficient exactly.
The numerical CSV retains up to 90 significant digits of each computed value.
Those digits are not all certified: the analytic error bound controls the
finite mathematical approximation, while the supplied implementation does
not enclose floating-point rounding errors. Printed article decimals are
shorter and must not be mistaken for values accurate to the much smaller
internal analytic bound.

## Status

The article contains conventional mathematical proofs, not Lean proofs.
The numerical checks do not prove its asymptotic or summability theorems.
The classical sectorial characterization of summability is cited and applied,
not presented as a new general theorem. The model-specific bridge and sharp
summability application are proposed contributions; global originality and
priority have not been independently certified. No named longstanding
conjecture is claimed solved. No ProveIt repository files were modified.
