# Global radial monotonicity for leading-index-one double polylogarithms

Research continuation prepared for Vladimir Reshetnikov's ProveIt program,
10 October 2026.

## Principal theorem

For every real b>0, the normalized imaginary-zero coordinate
eta_(1,b)(rho)=cos(theta_(1,b)(rho))/rho is strictly decreasing on 0<rho<=1
when b>1, strictly increasing when 0<b<1, and exactly 1/2 when b=1.
This proves the complete leading-index-one branch of the full-radius
conjecture in the inspected manuscript section. It is not merely a local
Taylor coefficient result.

The proof converts the imaginary-part zero to the unique mode of a
Cauchy-smoothed concave Green density, proves a reflected single-crossing
property, and separately converts the inverse-height sign to the disk-radial
sign. The article also proves a general Student-type mode-flow theorem,
all odd central moment signs, a global outer-radius cutoff for b>=1,
Hurwitz-shifted monotone sectors, and exact generating identities over all
odd/even inner orders.

## Files

- `article.pdf` and `article.tex`: the complete 23-page research article.
- `integration/05-leading-one-global-radius.tex`: additive manuscript
  fragment with the full proof of the main radial result and moment corollary.
- `integration/INTEGRATION.md`: placement and narrowly scoped status changes.
- `verification/verify_exact.py`: standard-library exact finite tests and
  rigorous rational root-bracket certificates.
- `verification/verify_symbolic.py`: five independent symbolic checks.
- `verification/core_numeric.py`, `verification/verify_numeric.py`:
  explicitly non-certified floating-point diagnostics and figure generation.
- `data/`: bracket inputs and separate exact, symbolic, and numerical receipts.
- `figures/`: the two figures in editable/reproducible PDF and PNG form.
- `AUDIT.md`, `PROVENANCE.json`, `requirements.txt`: scope and reproduction.

## Executed checks

1,938 exact finite coefficient/moment checks passed; 18 root brackets of
width 3e-10 were certified with rational arithmetic and an explicit infinite
series bound. These include b=1/4 and b=1/2 as well as integral inner orders.
Five symbolic identities passed. Twenty-four quadrature values were compared
with independent 70-digit direct-series evaluations; their maximum observed
absolute discrepancy was 3.38e-12. A 606-point root grid agreed with the
proved directions. The floating-point checks are not interval certificates.

## Reproduce without overwriting received evidence

From this directory, choose fresh output locations:

```sh
python verification/verify_exact.py --output-dir /tmp/polylog-exact
python verification/verify_symbolic.py --output-dir /tmp/polylog-symbolic
python verification/verify_numeric.py --output-dir /tmp/polylog-numeric \
  --figures-dir /tmp/polylog-figures
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Only the first verifier is standard-library-only. See `requirements.txt`
for the executed external-package versions. The article uses ordinary
LaTeX packages, including Latin Modern, AMS math/theorems, graphicx,
booktabs, hyperref, xurl, fancyhdr, microtype, and enumitem.

## Mathematical and source scope

The reference commit is `1539f353af88bdfd63292bb970ac8f585b15794d`.
The local-radius source was confirmed at that exact pin. The result is a
research proof, not independent peer review or proof-assistant verification.
No claim of worldwide priority is made. S6, S8, and the remaining
higher-outer-order radial questions are not solved by this package.
The incoming directory and intake instructions were inspected, but the
ZIP members were not available for content-level inspection. The precise
novelty claim is relative to the named canonical manuscript section.
No remote repository changes were made.
