# Sharp Stability Strata for Finite Fabius–Rvachev Deconvolution

**Colliding scales, vanishing factors, and optimal recovery exponents**  
Research report prepared for Vladimir Reshetnikov, 28 September 2026.

## Read the article

`article.pdf` is the compiled article; `article.tex` is its self-contained LaTeX
source, with an embedded bibliography and no external figure or source inputs.

The model is a known smooth compactly supported random background B plus at most
r unknown independent centered uniform factors a_i U_i. The Rvachev up law is a
special case of B. Parameters are nonnegative, sorted, and padded with zeros to
the fixed capacity r.

At a base configuration, let m_1,...,m_s be the multiplicities of the distinct
positive squared scales, and m_0 the number of zero slots. The article proves
that the optimal local pairwise inverse exponent in total variation is 1/M,
where M = max(m_1,...,m_s,2*m_0), omitting the last entry when m_0 = 0. The optimal
anchored exponent is instead 1 at a simple positive configuration and 1/2 at
every singular configuration. Both upper bounds and sharpness are proved.

Other contents include an exact leading density term for vanishing clusters,
finite cumulant reconstruction, noise-safe feasible fitting, deterministic
optimal-recovery bounds, a sampling upper bound, a formalization roadmap, and
eight proposed further research questions.

## Files

- `article.tex`, `article.pdf`: article source and compiled PDF.
- `verification.py`: exact symbolic checks and high-precision Fourier diagnostics.
- `requirements.txt`: pinned Python dependencies used for the checks.
- `verification_results.json`: output of the executed verification script.
- `data/chebyshev_checks.csv`: exact cancellation and leading-coefficient checks.
- `data/sharpness_scaling.csv`: 100-digit pointwise Fourier scaling diagnostics.
- `SOURCE_AUDIT.md`: repository snapshot, source scope, and external bibliography.
- `VALIDATION.md`: build, rendering, and mathematical verification boundaries.

## Reproduce the calculations

Python 3.10 or newer is required. The recorded run used Python 3.13.5.

```sh
python -m pip install -r requirements.txt
python verification.py --output-dir .
```

The script raises an error on a failed assertion and regenerates the JSON and
CSV outputs. All algebraic checks use exact SymPy arithmetic. The numerical
part uses mpmath at 100 decimal digits.

The code does not run an optimizer, estimate total variation by quadrature,
access an external service, or modify the ProveIt repository.

## Rebuild the PDF

Use a TeX distribution with pdfLaTeX and the packages named in the source,
including Libertinus, AMS mathematics, microtype, hyperref, cleveref, and xurl.
Run three passes from this directory to settle the contents and cross-references:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

TeX Live supplied these packages for the recorded build. No font files are
included in the archive. The source is independent of a local ProveIt checkout.

## Status and limitations

This is a theorem paper with full conventional mathematical proofs. The main
classification is presented as a result developed here, not as a claim of
worldwide publication priority or a solution of an unrestricted infinite-rank
problem. Classical Newton/cumulant and polynomial-root ingredients are identified
as such and cited. No independent peer review or Lean/Rocq verification is claimed.

The exact computations check finite algebraic examples; they do not replace the
all-orders proofs. The numerical measurements are characteristic-function
values at one frequency, NOT computed total variation distances. The sampling
result is an upper bound, not a statistical minimax theorem.

## Editorial amendments (ProveIt, 2026-09-29)

In the editorial pass after batch 54 of the repository-level `docs/incoming/`
drop zone (see `docs/incoming/README.md`), a later package of this tree was
found to take up two of its research questions. The article gains reciprocal notes; its
mathematical text is unchanged.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note
  (ProveIt, 2026-09-29)") is defined after the last theorem style.
- `article.tex`: after the research question "The optimal statistical
  experiment near collisions", a note records that
  `../Local_Minimax_Geometry_Uniform_Factors/` (filed 2026-09-29,
  unreviewed) proves, with a known positive Gaussian component added to a
  known bounded background, that the local minimax sampling rate at each
  collision pattern is `N^(-1/(2M))` with this article's `M` (there the
  known-variance denominator `max{Q, 2r}`), with matching likelihood lower
  bounds. For this article's compactly supported smooth background the
  question remains open.
- `article.tex`: after the research question "Unbounded capacity and
  tail-controlled infinite products", a note records that
  `../Gaussian_Dust_Christoffel_Recovery_Uniform_Factors/` (filed
  2026-09-29, unreviewed) treats infinite square-summable scale sequences
  for the Gaussian variance only (exact minimax risk `V/2` without tail
  control, uniform consistency exactly under uniformly vanishing
  squared-scale tails, Christoffel bias bounds exact for geometric
  spectra); the sharp modulus of recovery of the scale multiset is not
  determined there. Both notes are marked `% ed.`.
- `article.pdf`: rebuilt with three `pdflatex -interaction=nonstopmode -halt-on-error article.tex` passes (MiKTeX pdfTeX): 22 pages, as before, 677,500
  bytes; no error, undefined reference, rerun request, duplicate
  destination or overfull box; no Type 3 font.
