FABIUS--RVACHEV NEW FRONTIERS
-----------------------------

Repository snapshot audited
---------------------------
VladimirReshetnikov/ProveIt
commit b863b90ee74ec0405af2d67ad04c61824c3aea00
snapshot date: 2026-08-30
scope: Analysis/FabiusFunction/docs/**/*.tex, with the current coverage,
audit, archive, and frontier manifests used to distinguish canonical,
superseded, generated, proved, numerical, and conjectural material.

Main deliverables
-----------------
fabius_rvachev_new_frontiers.tex
    Current live source: 2,978 lines, 122,235 bytes, SHA-256
    e0015e424fe577c4aee3ea473ace71b67b9f250d5a96569dccd6dd03ebe20c98.
    It preserves the canonical
    preamble, cleaned-vector-figure and claim-status safeguards, the
    scalar-base-change Gram--Stieltjes and all-degree rational native Jacobi
    boundaries, and the detailed generic/Legendre determinant and finite-Gaunt
    crosswalk.  Its target inventory is all 129 public names across eleven
    modules, including the 25-declaration finite Gaunt tranche, the
    27-declaration integer-index zero-row square/factorial tranche, and the
    three finite Wigner-square Gram corollaries.  The current source is newer
    than the retained PDF described below; a rebuild is pending.

fabius_rvachev_new_frontiers.pdf
    Retained pre-update post-union artifact: 41 A4 pages, 780,141 bytes,
    SHA-256 9871ac93cce5d8ee1aa48e946f46dc2e19865fb33a1d2e3b9b8be01360318901.
    Exactly three strict serial passes from the frozen 2,863-line source
    produced 39, 41, and 41 pages.  It renders the former 99-name inventory but
    not the later 30-declaration Wigner-square addition.  The report embeds the
    five cleaned vector PDF figures.  Earlier 39-page and 41-page checkpoints
    remain recorded below as historical evidence.

fabius_frontier_experiments.py
    Fully commented 580-line exact/high-precision experiment. It computes
    rational moments and low-degree Jacobi data exactly, then computes
    high-degree data using mpmath without sampling the Fabius or up functions.

experiment_run.log
    Diagnostics from the publication run.

data/exact_low_degree.csv
    Exact rational moments, monic norms, Jacobi coefficients, product
    approximants, and central Christoffel approximants through the printed
    exact range.

data/jacobi_coefficients.csv
    Validated high-precision beta_1,...,beta_200 and asymptotic diagnostics.

data/pi_product_approximants.csv
    Jacobi-product and Christoffel approximants to pi.

figures/*.pdf and figures/*.png
    Five figures in dual format. The report embeds the cleaned one-page vector
    PDFs: all of their fonts are embedded and subset, and none contains Type 3
    fonts or raster images. The 2100 x 1260 PNG companions are preserved as
    supplemental package artifacts but are not embedded in the report.

CORPUS_AUDIT.md
    Scope, source strata, nonduplication method, and status boundary.

pdf_preflight.json
    Historical structural, geometry, font, text, build-log, and visual
    preflight for the retained post-union render.  It explicitly records that
    the current source/PDF pair is not synchronized.

SHA256SUMS.txt (retired)
    This package-local ledger was retired repository-wide on 2026-09-01. Its
    final 20-payload mixed source/retained-artifact snapshot remains recoverable
    from Git history; the historical verification did not assert source/PDF
    rendering parity.

Numerical publication run
-------------------------
python fabius_frontier_experiments.py \
    --degree 200 --dps 4800 --output .

The run independently checks exact rational output through degree 24.  It
found beta_1 < ... < beta_200 < 1/4.  This finite observation is recorded in
the report as evidence, not as a theorem.  The three regenerated CSV files
have 22, 201, and 101 lines respectively; their normalized LF bytes are
unchanged from the audited publication data.

Rebuild the PDF
---------------
Required: a reasonably complete TeX Live installation with pdflatex and the
Libertinus Type 1 packages. From this directory, the final publication build
must run all three passes:

pdflatex -interaction=nonstopmode -halt-on-error fabius_rvachev_new_frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error fabius_rvachev_new_frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error fabius_rvachev_new_frontiers.tex

After each rebuild, verify A4 page geometry, embedded/subset fonts, a positive
Libertinus font count, no Type 3 fonts, and the final page count before
refreshing the PDF preflight and checksum ledger.

Re-run the numerical experiment
-------------------------------
Required Python packages: mpmath, numpy, matplotlib.

A quick smoke run:

python fabius_frontier_experiments.py \
    --degree 24 --dps 500 --output /tmp/fabius-smoke

A higher target degree requires rapidly increasing precision because the
current monomial-basis recurrence is cancellation-prone.

The script writes CSV records with deterministic LF line endings and produces
the five vector plot PDFs.  Refresh the supplemental PNG companions after a
production run with:

for figure in jacobi_coefficients pi_approximants pi_product_error \
    scaled_jacobi_deficit zero_quantiles; do
  pdftocairo -png -singlefile -r 300 \
      "figures/${figure}.pdf" "figures/${figure}"
done

Retained post-union PDF verification (historical)
-------------------------------------------------
* The then-frozen 2,863-line, 115,122-byte source had SHA-256
  4eeea1a1cbe5497e6db3424a0c185f3a3be750f5816b22be5e7baed091753455.
  Exactly three halted serial pdflatex passes exited zero and produced 39, 41,
  and 41 pages.
* The retained 780,141-byte PDF has SHA-256
  9871ac93cce5d8ee1aa48e946f46dc2e19865fb33a1d2e3b9b8be01360318901.
  It is unencrypted PDF 1.5 with 41 zero-rotation A4 pages and A4 MediaBox,
  CropBox, BleedBox, TrimBox, and ArtBox values on every page.
* All 35 font rows are embedded and subset; five are Libertinus.  There are no
  Latin Modern or Type 3 fonts and no raster images.  The five embedded plot
  PDFs and five supplemental PNG companions retain their audited provenance.
* The final-pass log has no LaTeX/package warning, TeX error, unresolved
  reference/citation, duplicate label/destination, rerun request, or overfull
  box.  Its nine benign underfull notices are confined to the narrow
  claim-status table on page 7, which was inspected at full render size.
* Layout-preserving extraction produced 2,475 lines (144,752 bytes).  It
  contains all 99 public names across the nine inventoried modules, including
  all 25 generic/up-law finite Gaunt declarations.  The Gaunt formulas and
  nonclaim boundaries pass line-wrap-tolerant extraction checks.
* Pages 16--18, 21--31, and 36--38
  were visually inspected.  All five vector figures render cleanly on pages
  17, 22, 29 (two figures), and 30, with intact axes, legends, captions, and
  curves.
* At that checkpoint the fixed-scope checksum ledger verified all 20 payloads.
  The current ledger is refreshed independently for the newer source while
  retaining this PDF byte-for-byte.

Historical verification
-----------------------
* The arrival/pre-normalization checkpoint used a clean latexmk build with no
  unresolved references, duplicate labels, or overfull boxes. Its 37-page A4
  PDF was unencrypted and text-based; the 10 Type 3 font rows inherited from
  the then-current vector plots matched that checkpoint's recorded baseline.
* The subsequent normalized local checkpoint used exactly three strict serial
  pdflatex passes. Its 37-page A4 PDF had 35 embedded/subset font rows,
  Libertinus prose, no Type 3 or Latin Modern fonts, and five vector-only
  standalone figure PDFs. Layout-preserving text extraction retained all 41
  public names then inventoried, including the 18-name determinant crosswalk.
* The publication and normalized checkpoints were rendered and visually
  inspected in contact sheets, with changed/status/figure/final pages also
  checked at full-page resolution.
* Python byte-compilation and an independent degree-24 smoke run succeeded.

Historical 39-page cleaned-vector repository rebuild
----------------------------------------------------
* Clean strict serial pdflatex passes 1--3 produced 37, 39, and 39 pages.
* The final unencrypted PDF has 39 A4 pages, zero rotation, and A4
  MediaBox/CropBox/BleedBox/TrimBox/ArtBox on every page. All 35 font rows are
  embedded and subset; five are Libertinus; there are no Latin Modern or Type
  3 fonts and no raster images.
* The final-pass log has no LaTeX/package warning, overfull box, TeX error,
  unresolved reference/citation, duplicate label/destination, or rerun
  request. Its nine benign underfull notices are confined to the narrow
  claim-status table on page 7, which was checked at full render size.
* Layout-preserving extraction produced 2,363 lines (139,178 bytes).
  Whitespace-normalized PDF text contains all 99 public names across the nine
  scalar-naturality, native rational Jacobi, generic/Legendre determinant,
  executable rational, low-order values, and finite Gaunt modules inventoried
  in the report.
* Pages 1, 7, 11, 13, 14, 25, 27, 34, 35, and 39 were visually inspected; the title,
  corrected status table, complete rational/Gaunt crosswalk, vector figures,
  formalization roadmap, and final references page are unclipped and readable.
* At that checkpoint, the refreshed 20-entry checksum ledger included all five
  PNG companions and synchronized the TeX, PDF, README, CORPUS_AUDIT, and
  pdf_preflight entries.

Separate 41-page Gaunt checkpoint
---------------------------------
* A later local checkpoint used a frozen 2,864-line source, SHA-256
  1befebaf2f38048a0a1f8ae1a42476da6c8d05173b4651f4f10c0a96888c5f2e,
  and exactly three halted pdflatex passes to produce a 41-page A4 PDF,
  SHA-256 8f859f73bbaaf212a004278f8b3035d6f6add5a5de8deeb0bc3360ae9bb73446.
* That checkpoint embedded the five PNG plot companions, had 23 embedded and
  subset font rows including five Libertinus rows and no Type 3 fonts, retained
  all 76 focused declaration names (the prior 51 plus all 25 Gaunt names), and
  passed its then-current 20-entry ledger.
* Its status/crosswalk/Gaunt/reference/plot pages 2, 7, 13--14, 17, 22--23,
  25--27, 29--30, 37, and 41 were inspected, including all five plot placements
  on pages 17, 23, 29, 30, and 30.
* This is historical evidence only.  The current package retains the cleaned
  vector-PDF figure provenance.  It is superseded by the later retained
  post-union PDF checkpoint recorded above.  That checkpoint was synchronized
  only with its own frozen source; it is not a rendering of the current live
  TeX.

Claim status
------------
The arrival-time novelty screen was corrected after filing: the pinned
canonical representation frontier already contained the Nevai-limit,
J-fraction, Hankel, and Gauss--Padé program. Those strands are inherited
overlap; see CORPUS_AUDIT.md. The package remains standalone pending a
claim-by-claim deduplication.

The report distinguishes:
* results already present in the audited repository;
* new proofs or finite identities developed in the report;
* applications of classical external OPRL/Christoffel/Padé theorems after
  verifying their hypotheses for the up-law;
* high-precision observations; and
* explicitly labeled conjectures.

The post-snapshot Lean layer now proves executable rational Gaunt coefficients,
their real integral casts, finite Legendre product linearization, parity and
triangle-support zeros, and the finite rational and real up-law Gram-entry
sums.  It also defines the total rational integer-index zero-row square datum,
proves its central-binomial and factorial forms, identifies every rational and
real Gaunt coefficient with twice that datum, proves sharp support and
positivity, and derives the finite rational and real Wigner-square Gram sums.
This is not a signed Wigner-symbol or phase API.  Christoffel reconstruction, root results,
quadrature, Pade identification, infinite Jacobi products, and the report's
asymptotic claims remain outside Lean.

"New" means not found in the audited repository snapshot.  It is not a claim
of worldwide priority.
