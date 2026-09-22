# Gamma Functions over the Surreals

## A sharp convexity classification, flat nonuniqueness, and surcomplex phase domains

Research article, September 21, 2026. Prepared in response to the request to develop substantial results beyond the material in VladimirReshetnikov/Surreal.

## Files

- `article.pdf`: typeset article, with proofs and references.
- `article.tex`: complete standalone LaTeX source, including the bibliography.
- `code/verify.py`: exact rational/formal symbolic checks.
- `data/verification.json`: recorded results; **130 of 130 checks passed**.
- `data/source_audit.json`: scope and source record for the targeted research audit.
- `requirements.txt`: tested SymPy version.
- `Makefile`: optional build targets.

## Principal results

Let L0 be the Taylor–Stirling log-Gamma extension, M(x) the leading Conway monomial without its real coefficient, and pp(x) the purely infinite part. For a class assignment a on positive infinite monomials, set h_a(x)=a(M(x))*pp(x) at positive infinite arguments and zero at positive finite arguments.

The exact main theorem is:

**L0+h_a is convex on all positive surreals if and only if m*a(m) is finite for every positive infinite monomial m. In the affirmative case it is strictly convex.**

Every member of the family preserves the Gamma recurrence, normalization, finite Taylor extension, all ordinary finite Gauss multiplication formulas, all normalized finite-translation germs, and all positive-order fine derivatives of log-Gamma. This last statement is NOT an equality of the unnormalized derivatives of Gamma itself.

The explicit choice a(m)=lambda*exp(-m), with real lambda, gives distinct members whose differences are smaller than every ordinary inverse power at every infinite argument. They also preserve all ordinary-index signed first-omitted-term Stirling bounds.

Further results give the exact canonical finite-phase exponentiation domain for the constructed surcomplex log-Gamma on the tube Re(z)>0, Im(z) finite: at infinite Re(z)=x, the condition is Im(z)*log(x) finite. This is not a claim of maximal analytic continuation.

The Berarducci–Mantova scalar chain rule eliminates all infinitesimal locally constant discrepancies in the stated category, and all members of the monomialwise-linear family except the baseline. A different real-valued non-flat gauge shows why scalar compatibility alone is not a universal uniqueness characterization.

## Status

The established Taylor/transseries construction, Hahn summability, restricted analytic transfer, classical Gamma facts, and Berarducci–Mantova derivation are attributed inputs. The sharp coefficient classification and combined consequences are proposed contributions proved in the article.

This is not a claimed resolution of a named published open problem. The targeted search did not locate the exact classification, but it does not certify priority or absence from all literature. The article has not been independently refereed or verified in Lean or another proof assistant.

The 130 passing checks cover finite algebraic identities and finite sparse normal-form bookkeeping. They do not establish the all-scale surreal inequalities, class quantification, or support lemmas by computation.

## Build

A LaTeX distribution with `latexmk` and the packages named in the preamble is required. No external graphics, bibliography database, or custom font files are needed.

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Without latexmk, run `pdflatex -interaction=nonstopmode -halt-on-error article.tex` repeatedly until cross-references stabilize (normally three passes).

## Reproduce the checks

Python 3.9 or later is required. The recorded run used the versions saved in `data/verification.json`.

```text
python -m pip install -r requirements.txt
python code/verify.py --output data/verification.json
```

The script exits with status 0 only when all tests pass. It does not use numerical approximations to represent infinite surreal values.

## Repository inspection

Observed tree revision: `aa846271b4dcae2c055b216126a87210292ec19b`.

The audit inspected the repository tree and documentation catalogue, and read relevant differential-equations material to avoid duplicating existing results. It was not a complete line-by-line audit of every article and archived source. All repository operations were reads; no remote files were changed.
