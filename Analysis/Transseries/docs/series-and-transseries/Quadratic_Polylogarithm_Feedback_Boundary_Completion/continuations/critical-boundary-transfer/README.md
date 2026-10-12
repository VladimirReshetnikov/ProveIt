# Critical Boundaries of Quadratic Polylogarithm Feedback

**Research contribution prepared for Vladimir Reshetnikov, 12 October 2026.**

This package develops conventional proofs for

    u v(r) - v(r)^2/2 = Li_s(r exp(v(r))),   v(0) = 0,

at and beyond the critical boundary

    U_c(s) = sqrt(2 zeta(s) + zeta(s-1)^2),   s > 2.

It resolves the fixed-parameter boundary question explicitly left open in
Section 12, Question 1 of *Resonant Polylogarithm Transseries: Gamma Borel
Kernels, Cyclotomic Order Jets, and Sharp Dilogarithm Reversion* (11 October
2026). The exact constant there is proved, including integer orders and
complex dominance. This is a quadratic feedback model, not a blanket
identification with inversion of the general Fermi polylogarithm.

## Results

- Exact radius and unique dominant singularity in the strict and critical
  boundary regimes; absolute convergence on the boundary circle.
- The strict-boundary coefficient law with constant
  `w^(s-1)/(w-zeta(s-1))^s`, where `w=sqrt(u^2-2 zeta(s))`.
- Convergent two-generator inverse charts for every noninteger critical
  order, finite coefficient formulas, and exact minimum ramification indices.
- The critical order-three Lambert core with its quadratic normalization
  `5/2`; a finite Gamma-derivative formula for every inverse-logarithmic
  coefficient correction, including the first two in closed form.
- An exact missing `n^(-2)` term at critical order `s=5/2`, contrasted with
  an explicit nonzero `n^(-2)` term and a logarithmic obstruction to Puiseux
  structure at `s=4`.
- A finite-prefix and amplitude extension, retaining all constants and the
  marginal logarithmic shift.

The classical polylogarithm expansion, Lagrange inversion, singularity
transfer, and simply generated tree framework are credited. The repository
already contains related linear-core Hahn and marginal work. Global
publication priority for these model-specific refinements has not been
established. The full incoming corpus was not audited.

## Files

`article.tex` and `article.pdf` contain the article and proofs.
`code/verify.py` reproduces finite exact tests and numerical diagnostics.
`data/` contains the executed evidence, including symbolic marginal
polynomials and coefficient tables. `THEOREMS.json` identifies the
proof dependencies. `SOURCES.md` records the inspected sources and limits.
`INTEGRATION.md` and `integration_note.tex` propose non-destructive filing
and cross-reference wording. `BUILD_VALIDATION.json` records PDF validation.

## Replay

The recorded numerical/exact run used Python 3.13.5 with the packages
pinned in `requirements.txt`.

```sh
python -m pip install -r requirements.txt
python code/verify.py --output-dir replay --max-n 4096
```

The output directory must be absent or empty: delivered evidence is not
silently overwritten. On platforms where `numpy.longdouble` has a narrow
exponent range, the positive probability recurrence automatically switches
to the slower arbitrary-exponent mpmath implementation. The code does not
assume that Windows and Linux use the same long-double format.

The recorded run passed **293 exact assertions**, performed **21 original
coordinate-equation checks and six Lambert-core checks**, and evaluated
**49 coefficients across seven models through n=4096**. High-precision
constants and local diagnostics used 85 decimal digits; large-index
coefficient recurrences used 18-digit extended precision on the recorded
platform. These are not interval certificates. The theorem proofs do not
rest on fitting the numerical tables.

## Build the article

The source is self-contained and uses standard TeX Live packages.

```sh
make pdf
# Or run pdflatex -interaction=nonstopmode -halt-on-error article.tex three times.
```

`make verify OUT=replay2 MAX_N=4096` selects a new replay directory.
No custom font files, external images, or downloaded source articles are
needed or included.

## Research status and integration

This is an unrefereed manuscript with explicit conventional proofs, not a
Lean formalization. It resolves the cited question at fixed parameters;
uniform joint limits as `u -> U_c(s)` or `s -> 3` remain proposed research.
No new mathematical error was established in the accepted inspected source
claims. The editorial proposal is a scoped status update, not a correction
to an already-proved interior theorem. No remote repository files were
changed.

Suggested directory:

    Analysis/Transseries/docs/series-and-transseries/Quadratic_Polylogarithm_Boundary_Transfer/

with a cross-link from the Polylogarithms index. Review `INTEGRATION.md`
before editing any predecessor text.
