# Critical Complements in Fabius Conditioning

**Sharp information loss, geometric phase constants, and a logarithmic crossover**

A 24-page research manuscript prepared for Vladimir Reshetnikov, dated
30 September 2026 (25 pages with the editorial notes of 2026-09-30, 26 with those of 2026-10-01). The complete article is `article.pdf`; its editable
LaTeX source is `article.tex`.

## Research result

This continues the critical-complement question explicitly left open in
ProveIt's *Sharp Conditioning Laws for Uniform Random Series*. It resolves
its geometric-prefix version: fixed geometric ratio q, fixed exponential-tilt
phase rho, inequality conditioning at the tilted mean, and a prefix of n-m
bulk coordinates with m=o(n). The infinite boundary tail remains unobserved.

Theorem 2.1 gives a phase-sensitive two-term overlap expansion for fixed m,
a compact boundary correction with a controlled remainder, and relative
entropy through order 1/n with an O(n^-2) remainder. Theorem 2.2 proves the
leading overlap throughout the sublinear-complement regime and identifies
the crossover at m of order log n. Its coefficient is explicit through the
two real branches of Lambert W. Theorem 2.3 gives the entropy asymptotic for
growing m and identifies the fixed-complement information loss with the
mutual information of an additive exponential-noise channel.

All main results have conventional proofs. They are not Lean-certified or
externally refereed. The computations are diagnostics, not proof
certificates. Publication priority has not been established. Arbitrary
observation masks, general weights, and joint moving-q limits are not
silently included in the stated scope.

## Contents

- `article.tex`, `article.pdf`: manuscript, including proofs and bibliography.
- `code/verify.py`: deterministic floating-point boundary and finite-n checks.
- `code/make_figures.py`: builds the two figures and table fragments from data.
- `data/`: numerical CSV files, LaTeX tables, and the verification receipt.
- `figures/`: the two vector PDF figures used by the article.
- `CLAIM_STATUS.md`: proof and scope boundaries.
- `provenance.json`, `validation.json`: source and build records.
- `requirements.txt`, `Makefile`: reproduction support. The submitted
  checksum ledger `SHA256SUMS.txt` (18 entries) was verified in full on
  filing (batch 68 of `docs/incoming/`) and not kept; the delivered archive
  remains in the repository history (see `docs/incoming/README.md`,
  batch 68 row).

## Build the PDF

Use pdfLaTeX with standard TeX Live packages, including newtx, microtype,
the AMS packages, geometry, booktabs, fancyhdr, xurl, and hyperref:

```sh
make pdf
```

The figure PDFs and LaTeX table fragments are already supplied. Rebuilding
only the article needs neither Python nor network access. Font files are
not distributed.

## Rerun the calculations

```sh
python -m pip install -r requirements.txt
make diagnostics
```

`verify.py` uses Fourier inversion for the boundary CDF, exact analytic
exponential-tail formulas, and a signed Gamma formula for prefix densities.
There is no Monte Carlo. It computes the actual geometric-model formulas,
not a finite-simplex proxy, but finite grids, product truncation, numerical
integration, and floating-point arithmetic introduce approximations. The
reported grid agreement is not an interval-certified error bound.

For faster exploratory runs a smaller Fourier grid can be selected, for
example `python code/verify.py --grid-power 14`. The default is 15, with
comparison against a second grid of power 16. Since the editorial pass
(below) `code/verify.py` writes to `rerun/data/` and `code/make_figures.py`
reads `rerun/data/` and writes `rerun/figures/` and the two table fragments
in `rerun/data/`, so neither rewrites the recorded `data/` or `figures/`;
text and CSV outputs are LF on every platform. To regenerate the recorded
files, run both with `--output-dir .` from this directory. Fixed source and
library versions do not guarantee byte-identical figure PDFs across
platforms.

## Repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `0a543d5e435df885f78ca731d71856f3ee0ab2d4`.

The exact prior paths and the limited inspection scope are recorded in
`provenance.json`. No repository files were modified, and no Lean/Lake build
was run. The ten further research questions are in Section 10.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 66 to 68 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the programs `ed. (2026-09-30)`. The
title-page wording ("Prepared for Vladimir Reshetnikov") is kept as
delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble (the theorem counter is
  unchanged). Three notes:
  - Section 1.1, after the description of the two conditioning
    manuscripts: that description is incomplete. *Sharp Conditioning Laws
    for Uniform Random Series* also proves full-configuration rates for
    every positive summable weight sequence (its `cor:full-info`:
    `KL = (1/2) log(2 pi V) - 1 + o(1)` and
    `1 - TV ~ log V/(2 sqrt(2 pi V))`); for geometric weights
    `V = n + delta + o(1)`, so equation (2.21) (`eq:fullkl`) of Theorem 2.3
    re-proves that corollary's entropy statement without citing it, and the
    leading term of (2.16) coincides with its overlap statement. The article
    read only that manuscript's README and first 220 source lines;
  - end of Section 1.1: an independently written article under the same
    title, `../Critical_Complements_Fabius_Conditioning/` (batch 66,
    written against an earlier snapshot), answers the same question
    `q:critical` for different hidden coordinates: it hides the first `r`
    coordinates with the tail, for fixed `r`, and proves
    `sqrt(2 pi n)(1 - TV) = Lambda_n + r log Lambda_n + log K - log r! + 1 + o(1)`,
    every fixed Renyi order and an order-zero Renyi crossover. The two
    coincide only when nothing but the tail is hidden (`m = r = 0`): its
    tilt is `rho_CC q^{-n}`, so `rho_CC = rho/q`, its `log K` is
    `K_{q,rho,0}`, its `H_0` is `Z_0 = R_0 + E`, its `delta_0` is
    `Delta_0`, and its Theorem 3.4 (`thm:flatmain`) is (2.13)
    (`eq:correctedtv`) at `m = 0`, proved independently. Its
    `log K = 0.486134172...` (`q = 1/2`, `rho_CC = 1`) is `K_{1/2,1/2,0}` by
    (2.6) (outside the phase cell `1 <= rho < 1/q` used here), and
    `K_{1/2,1,0} = 0.944809318` of Table 1 is its `log K` at `rho_CC = 2`,
    both checked to 30 digits on filing. For `m, r >= 1` the theorems concern
    different marginals; "crossover", `K`, `h` and `delta` mean different
    things in the two articles. The growing boundary-adjacent complement
    (Theorems 2.2, 2.3) is not treated there; a growing early-coordinate
    complement is open in both (its logarithmic slice was treated later,
    for the overlap only; see the editorial amendments of 2026-10-01
    below);
  - after the proof of Proposition 3.1 (`prop:profile`): for `q = 1/2`,
    `F_q` is the Fabius function, machine-checked as
    `Fabius.ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal` and
    `Fabius.ProbabilityRepresentation.geometricUniformDensity_one_half_eq_rvachevUp`
    (`Analysis/FabiusFunction/Lean/FabiusFunction/ProbabilityRepresentation.lean`),
    which the article does not cite; no result of the article is
    formalized.

  No label was renamed or removed.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf` (MiKTeX
  pdfTeX 1.40.29): 25 pages (24 as delivered), with no error, undefined
  reference, multiply defined label, duplicate destination or overfull box;
  every font is embedded and none is Type 3. Theorem, section and equation
  numbers are unchanged, so `CLAIM_STATUS.md` stays correct (its "full-
  configuration entropy asymptotic" under Theorem 2.3 is the uniform-series
  corollary above, re-proved). The three pages carrying the notes were
  rendered and inspected.
- `validation.json`: `pdf_pages`, `pdf_bytes`, `pdf_sha256` and
  `tex_sha256` were recomputed for the filed files; its other fields
  describe the delivered build and are kept.
- `code/verify.py`, `code/make_figures.py`: they wrote the recorded `data/`
  and `figures/` in place. New option `--output-dir` (default `rerun/` in
  this package) for both; `make diagnostics` therefore writes `rerun/`.
  CSV, JSON and table outputs are written with LF line endings on every
  platform (CRLF on Windows before). A rerun of both amended programs on a
  copy (2026-09-30, `uv run --no-project --with numpy==2.3.5 --with
  scipy==1.17.0 --with matplotlib==3.10.8 python code/verify.py`, then
  `... code/make_figures.py`) passed and reproduced both table fragments byte
  for byte; the CSV files differ only in floating-point noise (relative at
  most 7.5e-8, in `corrected_kl_residual`; elsewhere at most 1.2e-11, apart from
  the noise column `grid_entropy_difference`), `verification.json` in three
  floats, and the re-rendered figure PDFs embed TrueType fonts only.
- `README.md`: the page count, the retired ledger, the output location, and
  this section.

## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 71 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-10-01)`. The mathematical text is unchanged.

- `article.tex`: a second unnumbered environment `ednotelater` ("Editorial
  note (ProveIt, 2026-10-01)") is defined after `ednote`. Two notes:
  - after Question 3, "Second-order crossover terms" (Section 10): the
    later article `../Second_Order_Critical_Complements_Fabius_Conditioning/`
    (filed 2026-09-30, batch 71, unreviewed) answers it in the compact
    window. It uses this article's tilt, for every `rho > 0`, and its
    "late" mask is the prefix `B_{n,m}` observed here (its "early" and
    "late" name the hidden coordinates). Uniformly for
    `c_0 log n <= m <= c_1 log n`, with `y_pm = y_pm(z_{n,m})` of (2.14),
    it proves
    `O_{n,m}/eps_n = m (y_+ - y_-) + [F] + [B]/m + O(m^{-2} + m^3/n)`,
    `F(y) = (log H(1 - 1/y) + 1)/(1 - 1/y)` with `H` the limit of (4.12)
    (`eq:Hdef`) and an explicit `B` built from `H`, `H'` and `H''`. The
    leading term is that of (2.15); the geometric phase reappears at
    constant order through `log H(1 - 1/y_pm)`. With `l = log n`,
    `c_n = m/l`, `Y_pm = y_pm(1/(2 c_n))` and
    `D = 1/(1 - 1/Y_+) - 1/(1 - 1/Y_-)` it separates `log(n/m)` from
    `log n`: `O_{n,m}/eps_n = l C(c_n) - (1/2) D log(c_n l) + [F] + O((log l)^2/l)`,
    with `C` of (2.17); for `m = c l + beta_n` with bounded `beta_n` the
    rounding contributes `beta_n C'(c) + o(1)`. For the mask hiding the
    first `m` bulk coordinates (that of
    `../Critical_Complements_Fabius_Conditioning/`, there for fixed `r`)
    `H` is replaced by `E exp(s R_0)`: same leading term, and for
    `m/log n -> c in (0, infinity)` the prefix observed here keeps
    eventually strictly less overlap. Thinner and thicker growing
    complements, uniformity as `c` tends to 0 or infinity, and entropy are
    not treated there;
  - after the 2026-09-30 note at the end of Section 1.1, which says that a
    growing early-coordinate complement is open in both articles: its
    logarithmic slice is now treated, for the overlap only, with a pointer
    to the note above.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf` (MiKTeX
  pdfTeX 1.40.29): 25 pages, as before, 462,709 bytes, with no error,
  undefined reference, multiply defined label, duplicate destination,
  overfull or underfull box; every font is embedded and none is Type 3.
  Theorem, section and equation numbers are unchanged, so
  `CLAIM_STATUS.md` stays correct. The two pages carrying the notes were
  rendered and inspected.
- `validation.json`: `pdf_pages`, `pdf_bytes`, `pdf_sha256` and
  `tex_sha256` were recomputed again for the filed files.
- `README.md`: the parenthesis after the 2026-09-30 bullet on the growing
  early-coordinate complement, and this section.

A second editorial pass the same day, after batch 72 of `docs/incoming/`,
added:

- `article.tex`: a third `ednotelater` note, after the question "Arbitrary
  observation masks" (Section 10): eight later unreviewed notes, written in
  one series against this article and filed beside it, answer parts of it,
  but not the sharp crossover through a complement cumulant function. For one
  kernel valid for every total-sum reweighting, mask order is convolution
  divisibility of the observed sums (`../Universal_Fabius_Mask_Criterion/`),
  for these geometric caps mask inclusion unless some power of `1/q` is an
  integer and otherwise classwise prefix counts
  (`../Arithmetic_Geometric_Mask_Order/`); for the conditioning here, a
  cap-dominating injection orders the information in every `f`-divergence
  (`../Exact_Fixed_Conditioning_Order/`) and, for masks of equal size, total
  variation strictly unless the cap multisets agree
  (`../Strict_Fabius_Conditioning_Order/`), so the prefix `B_{n,m}` has
  strictly less overlap than `{m+1, ..., n}` for every `rho > 0`, `n >= 2`
  and `1 <= m < n`; and `../Proportional_Fabius_Mask_Edgeworth/` expands total
  variation through order `1/n`, uniformly over masks, for hidden bulk
  fractions in a fixed compact subinterval of `(0, 1)`.
- `article.pdf`: rebuilt again with `latexmk -pdf` (MiKTeX pdfTeX 1.40.29):
  26 pages (25 before), 465,862 bytes, with no error, undefined
  reference, multiply defined label, duplicate destination, overfull or
  underfull box; every font is embedded and none is Type 3. Theorem, section
  and equation numbers are unchanged. The page carrying the note was rendered
  and inspected.
- `validation.json`: `pdf_pages`, `pdf_bytes`, `pdf_sha256` and `tex_sha256`
  recomputed for the filed files.
- `README.md`: the page count at the top and this paragraph.
