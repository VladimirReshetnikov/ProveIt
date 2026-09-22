# Holomorphic Dynamics on Surcomplex Halos
## Exact Flows and Sharp Small-Divisor Thresholds

Research manuscript prepared in response to a request for new, substantial
results in surcomplex analysis, dated September 21, 2026.

The package contains a standalone 30-page article with full proofs, an embedded
bibliography, and exact symbolic checks of its finite examples. It is an
AI-assisted, unrefereed manuscript. It does not claim to solve a named published
conjecture, to certify first priority, or to be formally verified.

## Main result

For an exact nonresonant diagonal unitary multiplier Lambda and a nonlinear
positive-support Hahn perturbation F(z) = Lambda z + f(z), Theorem 1.1 gives
necessary and sufficient conditions for universal normalized linearization
within each specified coefficient category. The quantity tau is the exponential
growth rate of the inverse ordinary complex homological divisors.

| Coefficient category | Universal criterion |
| --- | --- |
| Holomorphic on the same fixed finite polydisk | tau = 0 |
| Separate convergent germs, without a common radius | tau < infinity |
| Entire coefficients | tau < infinity |
| Polynomial coefficients | Nonresonance alone |
| Formal power-series coefficients | Nonresonance alone |

The proof treats arbitrary well-ordered positive supports in arbitrary
set-sized ordered abelian groups. It does not assume a rank-one value group,
countable support, or a finitely generated grid. A finite word certificate
bounds the input coefficient functions and homological inversions relevant to
one requested Hahn exponent. The paper proves radius and degree bounds and
constructs first-weight counterexamples establishing necessity.

Further results are a same-domain positive exponential/logarithm correspondence,
unique fractional iterates, equality of fixed-point ideals under every nonzero
integer iterate, the one-variable positive centralizer as an explicit group of
Hahn times, and a finite-order rotation/resonant-flow normal form. An explicit
non-Brjuno rotation with tau = 0 separates the result from ordinary analytic
linearization. A critical-scale example shows why finite-halo conclusions
cannot automatically be extended to infinite surcomplex arguments.

## Files

- `article.tex`: complete LaTeX source, with all bibliography entries embedded.
- `article.pdf`: compiled article, 30 pages.
- `code/verify.py`: sparse exact finite-jet checker.
- `data/verification.json`: all 21 passed checks and example expansions.
- `data/verification.txt`: the recorded console output.
- `data/environment.json`: tested Python/SymPy versions and page/check counts.
- `SOURCE_AUDIT.md`: literature provenance and the boundaries of the novelty assessment.
- `REVIEW_CHECKLIST.md`: load-bearing proof points and limitations for a reviewer.
- `requirements.txt` and `Makefile`: reproducibility aids.

## Build and run

A normal TeX Live installation with the packages named in the preamble suffices.
No external bibliography, figure, or font file is required.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The verifier requires Python 3.10 or later and SymPy. The recorded run used
Python 3.13.5 and SymPy 1.14.0. The requirements file pins that tested SymPy
version, not a claim about the latest available release.

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

Expected summary: `PASS: 21 exact finite-jet checks`.

The check suite uses exact rational and Gaussian-rational arithmetic, plus a
symbolic multiplier for four ordinary quadratic linearizer coefficients. The
one-parameter flow calculations are checked through degree six; two-parameter
calculations are checked through total parameter degree three. Total parameter
degree is NOT a Hahn valuation cutoff in a higher-rank ordered group.

## Scope and limitations

All infinite sums in the Hahn direction are strongly summable families:
well-ordered union of supports and finitely many contributions at each exponent.
They are not limits of partial sums in the fine surreal topology. Ordinary
analytic coefficient families are evaluated on finite halos; germ and formal
families are evaluated on the infinitesimal monad. Coordinate differentiation
treats all Hahn scalars as constants.

The logarithm of a formal diffeomorphism, the formal flow correspondence,
semisimple/unipotent patterns, and the classical small-divisor problem have
substantial published antecedents. Those ideas are credited, not claimed as
new. The proposed contribution is the precise arbitrary-support analytic
package and its sharp coefficient-category distinctions. The targeted
literature search is not an exhaustive priority determination.

The common-domain germ problem when 0 < tau < infinity is left distinct from
both preservation of an unchanged disk and radius-free convergence. The paper
does not claim that its coefficientwise radius lower bounds settle that problem.
The checks are not a Hahn-field implementation, a proof of the general support
or analytic theorems, or a Lean/formal verification.

The motivating repository was examined at commit
`39f2be6667ade51bca2b45daa47e289d69c09764`. No repository files were modified.
