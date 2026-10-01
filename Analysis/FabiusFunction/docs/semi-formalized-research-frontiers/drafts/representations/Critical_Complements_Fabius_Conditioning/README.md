# Critical Complements in Fabius Conditioning

**Logarithmic overlap, finite-memory corrections, and the order-zero Rényi crossover**

A 24-page research article prepared for Vladimir Reshetnikov, dated September 30,
2026 (25 pages with the editorial notes of 2026-09-30). This package extends the fixed-critical-complement regime explicitly posed
as a research question in ProveIt's *Sharp Conditioning Laws for Uniform Random
Series*.

## Main mathematical content

For S_q = sum(q^k U_k), tilt at t_n = rho q^(-n), condition the original law on
S_q <= E_Q[S_q], and observe coordinates r+1 through n, where r is fixed.
The omitted variance remains bounded while the observed variance is n + O(1).

The article proves an eventually exact likelihood-ratio reduction to the density
h_r of a tilted geometric boundary tail plus Gamma(r+1, 1). If
Lambda_n = log(2*pi*n)/2 and K = 1/E[exp(-rho*S_q)], the overlap satisfies

    sqrt(2*pi*n) * (1 - TV)
      = Lambda_n + r*log(Lambda_n) + log(K) - log(r!) + 1 + o(1).

A one-dimensional clipped-kernel formula has error O((log n)^3/n) on this scaled
level. An exact polynomial-tail identity supplies an all-orders inverse-logarithmic
expansion and isolates a smaller endpoint defect.

For every fixed positive Rényi order, the divergence is Lambda_n minus the
corresponding differential entropy of h_r, up to a vanishing error. At order zero
it instead tends to log(2). The article proves the crossover when alpha*sqrt(n)
tends to c: its limit is -log(exp(c^2/2)*Phi(-c)).

For r = 0, the residual from Lambda_n + log(K) + 1 is eventually positive and its
logarithm is asymptotic to -sqrt(log(1/q)*log(n)). This transfers Fabius endpoint
flatness into the overlap statistic.

The final section contains eight proposed research questions, including growing
complements, explicit finite-n remainders, sharper endpoint defects, inverse
reconstruction, uniform Rényi-order matching, multiple constraints, other digit
laws, and formal/interval verification.

## Files

- `article.tex`, `article.pdf`: complete manuscript source and compiled PDF.
- `code/verify.py`: exact algebra checks and numerical diagnostics.
- `data/`: exact rational records, CSV diagnostics, generated LaTeX tables, and
  the executed verification receipt.
- `figures/`: the three figures used in the manuscript.
- `CLAIM_STATUS.md`, `provenance.json`, `validation.json`: proof, novelty,
  source-inspection, and artifact-validation boundaries.
- `requirements.txt`, `Makefile`: reproduction support.
- The submitted checksum ledger `SHA256SUMS.txt` (20 entries) was verified in
  full on filing (batch 66 of `docs/incoming/`) and not kept; the delivered
  archive remains in the repository history (see `docs/incoming/README.md`,
  batch 66 row).

## Build the PDF

With pdfLaTeX, latexmk, and the required TeX Live packages installed:

```sh
make pdf
```

The source uses `libertinus` and `libertinust1math`, together with standard math,
layout, and hyperlink packages. The table fragments and figures are already
included, so building the PDF does not rerun the numerical calculations.
Font files themselves are not distributed.

## Reproduce the diagnostics

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

Since the editorial pass (below) this writes to `rerun/data/` and
`rerun/figures/` and leaves the recorded `data/` and `figures/` unchanged;
text outputs are written with LF line endings. To regenerate the recorded
files and then the PDF, run from this directory:

```sh
python code/verify.py --output-dir .
make pdf
```

The delivered run passed 228 exact symbolic assertions: 72 moment/cumulant
comparisons, 72 tail-polynomial differential identities, and 84 finite-simplex
integral identities. It also ran 24 geometric and 24 simplex crossover cases.
The sampled boundary mesh-refinement difference was approximately 7.20e-10.

The numerical work is deterministic, but floating-point libraries can produce
slightly different last digits and rendered figures on different platforms.
All figures use Matplotlib's default color cycle; there is no Monte Carlo run.

## Scope and status

The article supplies conventional mathematical proofs. The proposed new results
have not been compiled in Lean or independently refereed. Worldwide priority is
not certified. The fixed-r bounded-complement case is resolved here; a growing
number of omitted coordinates is not covered by the uniform error claims.
Classical tilting, gamma/simplex formulas, and leading small-deviation estimates
are not claimed as new.

The numerical calculations use ordinary floating point and are not interval
certificates. The infinite boundary is approximated by midpoint convolution,
and very large caps are removed from the bulk numerical surrogate. Exact
algebra checks must not be confused with verification of the asymptotic proofs.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 66 to 68 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the program `ed. (2026-09-30)`. The
title-page and `pdfauthor` wording ("prepared with ChatGPT for Vladimir
Reshetnikov") is kept as delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble (the theorem counter is
  unchanged). Two notes:
  - end of Section 1.1: a second, independently written article under the
    same title, `../Critical_Complements_Sharp_Information_Loss/`
    (batch 68), answers the same question `q:critical` for different hidden
    coordinates. It observes the prefix `{1, ..., n-m}` and hides the last
    `m` coordinates before the boundary with the tail, for every `m = o(n)`
    (a two-term overlap expansion and entropy to order `1/n` for fixed `m`;
    a Lambert-W leading overlap changing regime at `m ~ log n`, and entropy
    `(1/2) log(n/m) - 1/2 + o(1)`, for growing `m`); this article hides the
    first `r` coordinates with the tail, for fixed `r`. The two coincide
    only when nothing but the tail is hidden (`r = m = 0`): with that
    article's tilt `rho' q^{-(n+1)}`, `rho = rho'/q`, its `K_{q,rho',0}` is
    `log K` here, its `R_0 + E` is `H_0`, its `Delta_0` is `delta_0`, and its
    corrected overlap (Theorem 2.1, `eq:correctedtv`, at `m = 0`) is
    Theorem 3.4 (`thm:flatmain`), proved independently. On filing,
    `log K = 0.486134172...` (`q = 1/2`, `rho = 1`) was reproduced from that
    article's formula at `rho' = 1/2`, and its tabulated `K = 0.944809318`
    (`rho' = 1`) equals `log K` here at `rho = 2`, both to 30 digits. For
    `r, m >= 1` the theorems concern different marginals (the
    `r log Lambda_n - log r!` terms come from the `Gamma(r+1,1)` part of
    `H_r`; there the hidden sum is bounded); "crossover", `K`, `h` and
    `delta` mean different things in the two articles. The growing
    early-coordinate complement (the first question of Section 13) stays
    open;
  - end of Section 2.1: the identification of the `q = 1/2` law with the
    Fabius function is machine-checked as
    `Fabius.ProbabilityRepresentation.weightedSumCDF_eq_fabiusReal` and
    `Fabius.ProbabilityRepresentation.geometricUniformDensity_one_half_eq_rvachevUp`
    (`Analysis/FabiusFunction/Lean/FabiusFunction/ProbabilityRepresentation.lean`),
    which the article does not cite; no result of the article is formalized.

  One marked change: the title page no longer sets page anchors (it is
  numbered 1 like the following page), which removes the delivered source's
  one duplicate-destination warning. No label was renamed or removed.
- `article.pdf`: rebuilt from the amended source with `latexmk -pdf` (MiKTeX
  pdfTeX 1.40.29): 25 pages (24 as delivered), with no error, undefined
  reference, multiply defined label, duplicate destination or overfull box;
  every font is embedded and none is Type 3. Theorem, section and equation
  numbers are unchanged, so `CLAIM_STATUS.md` stays correct. The two pages
  carrying the notes were rendered and inspected.
- `validation.json`: `pdf_pages`, `pdf_bytes`, `pdf_sha256` and the
  `article.tex` entry of `effective_tex_input_sha256` were recomputed for the
  filed files; its other fields describe the delivered build and are kept.
- `code/verify.py`: it wrote `data/` and `figures/` in place on every run.
  New option `--output-dir` (default `rerun/` in this package), receiving
  `data/` and `figures/`; text and CSV outputs are written with LF line
  endings on every platform (CRLF on Windows before). A rerun of the amended
  program on a copy (2026-09-30, `uv run --no-project --with numpy==2.3.5
  --with scipy==1.17.0 --with sympy==1.14.0 --with mpmath==1.3.0 --with
  matplotlib==3.10.8 python code/verify.py`, which resolved Python 3.13.5)
  passed the 228 exact checks and reproduced `exact_algebra.json`, both
  other CSV files and the three table fragments byte for byte;
  `overlap_diagnostics.csv` differs only in the last digits (relative
  difference at most 3.0e-10) and `verification.json` in two floats in the
  16th digit (floating-point noise); the PNG figures are re-rendered.
- `README.md`: the page count, the retired ledger, the output location, and
  this section.
- Recorded, not changed: `provenance.json` describes its pinned reference as
  "not asserted to be a commit ID"; it is a commit of this repository (the
  last write of batch 64).
