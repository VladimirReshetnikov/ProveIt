# Reversion Beyond Archimedean Valuations

**Strong Hahn convergence, sharp Newton depth, and minimal finite coefficient certificates**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.
The compiled article has 28 A4 pages. It contains full conventional proofs,
worked examples, an exact verification report, a formalization dependency
plan, and nine further research questions.

## Research target

The article addresses the question on reversion beyond Archimedean exponent
groups in the ProveIt package **Support-Controlled Reversion and the Exact
One-Exponential Substitution Group**. The inspected repository snapshot is
`3f2d57344dc6f0b3dfa376f9490bfe13d1beb81e`.

The mathematical setting is a Hahn power-logarithmic ring with an explicitly
specified fixed derivative shift and additive differential character. This
qualification matters: the paper is not a theorem about every possible
natural derivation on a full logarithmic-exponential transseries field.

## Main results

* Positive-word support depth replaces an Archimedean valuation bound.
  Ordinary integer-indexed Lagrange reversion remains valid.
* Small-coefficient implicit systems admit strongly Hahn-convergent Picard
  and Newton iterations. Newton depth improves from r to 2r+1, giving
  r_n = 2^(n+1)-1; a rational scalar model attains every bound.
* Valuation convergence holds uniformly for this support class exactly when
  multiples of the minimum support exponent are cofinal.
* Every finite coefficient request factors through an explicitly described
  minimal finite-rank quotient algebra. Finite supports admit rational
  word-budget certificates, even in non-Archimedean groups.
* A rank-two support has exact quadratic depth and no positive real additive
  grading. More generally every positive-integer superadditive depth profile
  is realized in rank two; maximum-order contributions can be noncancelling.

Generalized-series implicit-function and inversion theories are classical.
The paper does not claim that general Hahn inversion is a new discovery,
or that a comprehensive literature-priority check has established first
publication of each sharper formulation.

## Files

`article.tex` — standalone LaTeX source, including bibliography and tables.

`article.pdf` — compiled, visually checked 28-page article.

`verify.py` — exact rational and polynomial verification program.

`verification_results.json` — output of the executed verification run.

`requirements.txt` — tested Python dependency.

`build.sh` — runs verification and compiles the article in three passes.

`PROVENANCE.json` — pinned source paths and scope of repository inspection.

`BUILD_REPORT.json` — compilation, rendering, and finite-check status.

## Reproduction

Python 3.10 or newer is required by the verification program. The recorded
run used Python 3.13.5 and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

On a system with a POSIX shell, `sh build.sh` runs the same workflow using
`python3`. No repository checkout, external images, or bibliography database
is needed. The verification program performs no network requests and uses
no floating-point approximations.

## Executed checks

The scalar Newton example was checked through ordinary degree 130, including
first error degrees 1, 3, 7, 15, 31, 63, and 127. A resonant power-logarithmic
inverse was checked in all 27 nonconstant blocks of total degree at most six:
Lagrange, Picard, and Newton agree and both composition residuals vanish.
The finite support certificate has exact depth seven and an 18-block divisor
quotient. Independent integer-partition enumeration checks 495 quadratic
profile targets and 49 factorial-profile targets.

These finite checks audit formulas and examples; they do not replace the
quantified proofs. No new Lean module was compiled. Analytic realization,
Borel summability, resurgence, and polynomial total running time are not
claimed.
