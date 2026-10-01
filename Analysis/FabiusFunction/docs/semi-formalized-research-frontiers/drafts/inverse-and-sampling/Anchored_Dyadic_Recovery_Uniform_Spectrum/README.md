# Anchored Recovery of the Dyadic Uniform Spectrum

A research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Main results

For sums of independent centered uniforms with decreasing summable half-lengths,
the inverse modulus anchored at the exact dyadic spectrum a_j = 2^(-j) is

    exp[-Theta(sqrt(log(1/epsilon)))].

This holds for total variation and Kolmogorov distance. The lower construction
preserves the predecessor's exact variance and all its derivative bounds, and
remains geometrically separated for any fixed ratio rho > 1/2. Every fixed
leading prefix, in contrast, is locally Lipschitz-stable under only a common
support bound on the unknown entire spectrum. The article also proves a
matching-order testing sample-complexity theorem and honest confidence-set
contraction at the reference.

The exponent 1/2 is sharp. The leading stretched-exponential constant is not
determined. The pairwise modulus, the exact-support-endpoint restriction, and
the separation boundary rho = 1/2 are left open. (The boundary rho = 1/2 was
later answered at the dyadic reference by
`../Lacunarity_Boundary_Geometric_Uniform_Spectra/`, batch 68: a sharp
`Theta(sqrt(epsilon))` modulus; see the editorial amendments below.)

## Contents

- article.tex and article.pdf: self-contained article, complete proofs, references,
  explicit error formulas, numerical tables, proof audit, and nine further questions.
- code/verify.py: exact rational regression checks and separately labeled
  high-precision diagnostics.
- data/: recorded verification output and CSV evaluations of the analytic bounds.
- notes/proof_audit.md: sensitive proof steps and limitations.
- notes/sources.md and notes/provenance.json: repository snapshot, source identity,
  source-question mapping, and primary literature.
- notes/validation.json: build and PDF validation record.
- requirements.txt, Makefile: reproduction helpers. The submitted SHA256SUMS was
  verified in full (14/14) on filing (batch 57 of `docs/incoming/`) and not kept; the delivered archive remains in the repository history (see `docs/incoming/README.md`, batch 57 row).

## Build

From this directory, run:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

Alternatively run `latexmk -pdf article.tex` or `make pdf`. No shell escape,
Python execution, network access, or separate bibliography processor is needed.
The standard TeX packages listed in the preamble must be installed.

For the computations (on the ProveIt machine use `uv run` or `py` rather than
bare `python`):

    uv run --no-project --with mpmath==1.3.0 python code/verify.py

The script resolves output paths relative to itself. It can also be invoked by
absolute path from another directory. It writes the four data files to
`data-rerun/`, or to the directory given by `--output-dir`; `data/` holds the
recorded run and is overwritten only when `--output-dir` points at it.

## Verification status

The recorded run passed 949 finite exact-arithmetic checks. The high-precision
root computations and decimal evaluations are diagnostics, not interval
certificates. A displayed TV upper bound is not an actual TV distance obtained
by numerical quadrature. The mathematical assertions for all n rely on the
written proofs, not extrapolation from finite tests.

The manuscript is an unrefereed, AI-assisted conventional mathematical proof.
It is not Lean- or Rocq-checked; no formal build was performed. Exhaustive
literature priority has not been established. No repository file was modified.

## Relation to ProveIt

The specific predecessor is Recovering_Uniform_Factors_Fabius_Rvachev/article.tex
in the inverse-and-sampling research collection. The pinned repository commit is
39472967ce67566d7c530fd5b8d6a3a95e68fe22. See notes/sources.md for the full path
and the exact questions addressed. This article does not claim to originate
qualitative identifiability of uniform-convolution spectra.

## Editorial amendments (ProveIt, 2026-09-29)

Made in the editorial pass after batch 57 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-29)`, every change to the program `ed. (2026-09-29)`.
The byline "prepared with ChatGPT" is kept as delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-29)" is defined in the preamble. A note after the
  question-mapping table of Section 10.2 gives the Lean crosswalk the article
  does not cite: the zero multiplicity `1 + v_2(m)` is
  `Fabius.analyticOrderAt_rvachevFourierProduct_int`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/IntegerZeroAnalyticOrder.lean`),
  the power-of-two divisor count behind the divisor inversion is
  `Fabius.dyadicZeroMultiplicity_ge_succ_iff_pow_two_dvd`
  (`DyadicZeroMultiplicity.lean`), the derivative norms `2^(r(r+1)/2)` are
  `Fabius.isGreatest_abs_iteratedDeriv_rvachevUp` (`GlobalBounds.lean`), the
  variance `1/9` is `Fabius.integral_sq_mul_rvachev_eq_one_ninth`
  (`DyadicSpecializations.lean`), and exact identifiability from zero orders
  is `GeneralizedRvachevIdentifiability.lean`; no quantitative statement of
  the article is formalized. A second note, after Research question 7
  ("Square-summable spectra and Gaussian confounding"), records that the
  predecessor's corresponding question is answered for the Gaussian-variance
  functional by `../Gaussian_Dust_Christoffel_Recovery_Uniform_Factors/`
  (filed after this article's snapshot), in a model with a known smooth
  compactly supported background: exact minimax risk `V/2` without a tail
  restriction; recovery of the scales themselves is not treated there. The
  paragraph "How to reproduce the package" now says where the program writes.
- Reciprocal notes now stand under the questions "Pointwise recovery of the
  exact dyadic spectrum", "Geometrically separated classes", "Fixed leading
  factors versus the complete sequence" and "Matching statistical upper
  bounds" of `../Recovering_Uniform_Factors_Fabius_Rvachev/article.tex`,
  which this article answers at the dyadic reference (the last one in
  anchored testing form only).
- Relation not cited by the article: at the dyadic reference only, it bears
  on the problems "Unbounded capacity and tail-controlled infinite products"
  of `../Sharp_Stability_Strata_Fabius_Rvachev_Deconvolution/` and "Growing
  capacity and the infinite-factor transition" of
  `../Gaussian_Confounding_Sharp_Recovery_Uniform_Factors/`. Those concern a
  known background with an unknown finite or infinite factor list; here the
  whole spectrum is unknown and one reference is fixed.
- `article.pdf`: rebuilt with `latexmk -pdf -interaction=nonstopmode
  -halt-on-error article.tex` (MiKTeX 26.2 pdfTeX 1.40.29): 23 pages (22 as delivered; the
  notes add one), 512,369 bytes; no error, undefined reference,
  duplicate destination or overfull box; no Type 3 font. The pages carrying
  the notes were rendered and inspected. `notes/validation.json` is the
  delivered build record and describes the 22-page PDF.
- `code/verify.py`: new option `--output-dir`, default `data-rerun/` beside
  `data/`, so a plain run (and `make check`) no longer rewrites the recorded
  evidence; all four outputs are written with LF line endings on every
  platform (the delivered program wrote CRLF CSV files everywhere and CRLF
  JSON/TXT on Windows). A rerun of the amended program on a copy
  (2026-09-29, `uv run --no-project --python 3.13.5 --with mpmath==1.3.0
  python code/verify.py`, under a second) passed all 949 exact checks and
  reproduced the four files in `data/` byte for byte.
- `data/analytic_bounds.csv`, `data/rouche_thresholds.csv`: delivered with
  CRLF line endings and normalized to LF on filing (batch 57).
  `data/verification.txt` is a byte copy of `data/verification.json` (the
  program writes the same report twice), not a separate console log.
- `README.md`: the ledger line under "Contents", the computation command and
  output location, and this section.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 66 to 68 of `docs/incoming/` (see
`docs/incoming/README.md`); the changes to the source are marked
`% ed. (2026-09-30)`.

- `article.tex`: a second unnumbered environment `ednotelater` ("Editorial
  note (ProveIt, 2026-09-30)") is defined after `ednote`. After Research
  question 3 ("The sharp separation boundary rho = 1/2") a note records
  that `../Lacunarity_Boundary_Geometric_Uniform_Spectra/` (batch 68,
  written against this article, same normalization) answers it: under
  `a_{j+1} <= a_j/2`, `sup_j |a_j - 2^{-j}|^2 <= (75/4)(19/675 - E X_a^4)`,
  so the anchored modulus at `rho = 1/2` is `Theta(sqrt(epsilon))` in total
  variation and Kolmogorov distance, with matching deleted-factor witnesses
  in `K`; at the boundary it also answers Research question 4 negatively
  (`sum_j a_j <= 1`, with equality only at `a^0`) and Research question 5
  inside its critical cone only (`Theta(2^r)`). The pairwise modulus, the
  exact-support question with slack and the prefix constants on `A_L`
  remain open.
- `article.pdf`: rebuilt the same way: 23 pages, as before, with no error,
  undefined reference, multiply defined label, duplicate destination or
  overfull box; no Type 3 font. The page carrying the note was rendered and
  inspected.
- `README.md`: the sentence on open problems under "Main results" (a
  parenthesis) and this section.
