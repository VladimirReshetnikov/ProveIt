# Flat Boundaries Preserve Information

## Sharp recovery of uniform convolution factors without Gaussian smoothing

Research report prepared for Vladimir Reshetnikov, 29 September 2026.

`article.pdf` is the 21-page compiled article. `article.tex` is its standalone
LaTeX source, with an embedded bibliography and no external figure inputs.

## Main results

For a known background B = sum_j b_j U_j with infinitely many positive b_j,
sum_j b_j < infinity, and independent U_j uniform on [-1,1], the article
proves an exact all-order Hellinger moment-matching expansion. The Rvachev
up density corresponds to b_j = 2^(-j).

If two fixed perturbation laws have every absolute moment finite and agree
in moments below order r, their squared Hellinger distance after scaling
by h and convolving with the background is

    Delta_r^2 * J_r(f) * h^(2r) / (4 * (r!)^2) + o(h^(2r)),
    J_r(f) = integral (f^(r))^2 / f.

The paper proves that every J_r(f) is finite and positive and proves a
strong L2 square-root expansion. It does not assert finite chi-square
divergence relative to the unsmoothed law: that divergence is infinite in
the single-added-uniform example.

For fixed capacity m, ordered half-lengths in [0,1], a known background,
and independent observations, the sharp minimax expected-loss rates are:

- Known Gaussian variance, including exactly zero: n^(-1/(4m)) for scales.
- Unknown Gaussian variance in [0,V], V > 0: n^(-1/(4m+4)) for scales.
- In that unknown-variance model: n^(-1/(2m+2)) for variance itself.

The unknown-variance lower bounds are realized by pairs approaching (a,v)=0;
one member has v=0 exactly. Detection against no uniform factors has critical
orders n^(-1/4) and n^(-1/8), respectively.

A separate theorem gives the exact finite-uniform boundary trichotomy:
h^M, h^(2r) log(1/h), or h^(2r) for squared Hellinger distance according as
M < 2r, M = 2r, or M > 2r. The article includes explicit constants and an
identifiable moment-indeterminate example with beyond-all-powers separation.

## Relationship to earlier work

This continues the explicitly unresolved statistical lower-bound issue in
ProveIt's `Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution` report and
Research Question 1 of the companion report `Gaussian Confounding and Sharp
Recovery of Uniform Convolution Factors`.

Repository snapshot:

    9b24a3a8d545af9624f6ac455f5b548be62818b6

The companion report was read from the user's Library, not represented as
part of that pinned repository. The paper credits its shifted-moment algebra
and distinguishes classical higher-order Fisher information from the
Hellinger and zero-noise conclusions developed here. See SOURCE_AUDIT.md.

## Files

- `article.tex`, `article.pdf`: standalone article source and compiled PDF.
- `verification.py`: exact algebra and numerical spline/Hellinger checks.
- `requirements.txt`: pinned dependencies for those checks.
- `verification_results.json`: recorded results of the completed run.
- `data/hellinger_diagnostics.csv`: twenty numerical diagnostic rows.
- `SOURCE_AUDIT.md`: source scope, provenance, and comparison boundaries.
- `VALIDATION.md`: build, rendering, computation, and proof-status record.
- `build.sh`: three-pass pdfLaTeX build command.

## Rebuild the article

A TeX installation with pdfLaTeX, Libertinus, AMS mathematics, microtype,
fancyhdr, hyperref, cleveref, booktabs, enumitem, and xurl is sufficient.
No font files are distributed.

```sh
sh build.sh
```

Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error article.tex`
three times from this directory.

## Reproduce the checks

Python 3.10 or newer is suitable. The recorded run used Python 3.13.5.

```sh
python -m pip install -r requirements.txt
python verification.py --output-dir ./recomputed
```

The program creates the output directory, then writes its JSON and CSV there.
For only the exact checks:

```sh
python verification.py --exact-only --output-dir ./exact_recomputed
```

A failed exact assertion raises an error. The default numerical precision is
60 decimal digits; `--dps 90` raises it. Numerical integration is not an
interval certificate. Run into a separate output directory to preserve the
delivered evidence files for comparison.

## Status and limits

The article contains full conventional mathematical proofs, not Lean or
Rocq formalization. No independent peer review or worldwide publication
priority is claimed. The finite exact checks do not establish the all-order
theorems, and the numerical diagnostics do not simulate a minimax risk.
No numerical value for J_r(up) is claimed. Constants are not uniform in a
growing capacity or changing background, and mixed collision strata remain
among ten precisely formulated further research questions.
