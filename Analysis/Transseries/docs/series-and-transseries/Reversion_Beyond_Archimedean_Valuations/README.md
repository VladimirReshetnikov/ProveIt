# Reversion Beyond Archimedean Valuations

**Strong Hahn convergence, sharp Newton depth, and minimal finite coefficient certificates**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.
The compiled article has 30 A4 pages with the editorial notes of 2026-09-29
(28 as delivered). It contains full conventional proofs,
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

`article.pdf` — compiled, visually checked article (30 pages since the
editorial amendments below).

`verify.py` — exact rational and polynomial verification program.

`verification_results.json` — output of the executed verification run.

`requirements.txt` — tested Python dependency.

`build.sh` — runs verification (output to `build/`) and compiles the
article in three passes.

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
`python3` (or the interpreter named by `PYTHON`), except that it writes the
verification output to `build/verification_results.json` and leaves the
recorded `verification_results.json` untouched. No repository checkout, external images, or bibliography database
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

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed unedited in batch 48 (see `docs/incoming/README.md`).
The following changes were made afterwards; each change to the article is
marked in the source by a `% ed. (2026-09-29)` comment, and every visible
addition is an unnumbered "Editorial note (ProveIt, 2026-09-29)", so no
theorem, lemma or equation number changed.

- `article.tex`:
  - Preamble: the unnumbered `ednote` environment.
  - End of Section 1.1: a scope note. "We resolve" means the reversion
    article's question "Beyond Archimedean exponent groups" for fixed-shift
    power–logarithmic derivations; it is not the first non-Archimedean Hahn
    reversion in the repository (the surcomplex analysis volume's
    `e:lem-reversion` already has existence and the same Lagrange sum
    without logarithmic blocks). The Newton law called "sharper" in the
    abstract is, for real exponents and `h = 1`, the reversion article's
    `eq:newtonrate` (Theorem 4.1, `thm:newton`) in word-depth units, which
    the article did not credit. The note also names the uncited canonical
    remarks `plt:rmk:ext-archimedean` and `plt:rmk:ext-neumann-general`.
  - After Lemma 2.2 (`lem:words`): the lemma is already formalized in Lean
    as `Surreal.HahnSeries.finite_words_of_sum_eq`
    (`Algebra/SurrealNumbers/Surreal/HahnSeries/Neumann.lean`),
    `Surreal.HahnSeries.finite_wordsWithSum` and
    `Surreal.HahnSeries.isPWO_closure_of_pos`
    (`Algebra/SurrealNumbers/Surreal/HahnSeries/NeumannWords.lean`), with
    `Surreal.HahnSeries.neumann_positive` combining both halves.
  - After Theorem 4.2 (`thm:implicit`): the identity of its Newton rate
    with the predecessor's `eq:newtonrate`.
  - After Theorem 8.1 (`thm:reversion`): the same Lagrange sum is the
    predecessor's `thm:LB` / `eq:blockLB` and the surcomplex
    `e:lem-reversion`; what is new is the power–logarithmic block calculus
    with shift data `(h, χ)`.
  - Bibliography: two entries, `EdSurcomplex` and `EdSurrealLean`.
- `article.pdf`: rebuilt from the amended source (`latexmk -pdf`): 30 pages,
  no errors, undefined references, multiply defined labels, duplicate
  destinations or overfull boxes. `BUILD_REPORT.json` is the record of the
  delivered 28-page build and was left unchanged; it stores no digests.
- `verify.py`: `verification_results.json` is written with `newline="\n"`,
  so a rerun on Windows no longer produces CRLF. A rerun of the amended
  program (Python 3.13.5, SymPy 1.14.0) on a copy reproduced the filed JSON
  byte for byte.
- `build.sh`: it no longer overwrites the recorded
  `verification_results.json`; the verification rerun writes
  `build/verification_results.json` (ignored by git). The interpreter can be
  chosen with `PYTHON` (default `python3`). A run of the amended script on a
  copy left `article.tex` and `verification_results.json` unchanged.
