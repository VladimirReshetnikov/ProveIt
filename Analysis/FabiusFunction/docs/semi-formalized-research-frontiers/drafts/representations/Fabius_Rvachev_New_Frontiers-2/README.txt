FABIUS--RVACHEV NEW FRONTIERS
=============================

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
    Complete 2,827-line A4/27 mm/Libertinus LaTeX report. The merged source
    preserves the canonical preamble, vector-figure and claim-status
    safeguards, retains
    the current scalar-base-change Gram--Stieltjes and all-degree rational
    native Jacobi boundaries while incorporating the detailed generic and
    Legendre Gram-determinant Lean crosswalk. It now inventories all 99 public
    names across nine relevant modules: the 22-declaration executable rational
    Legendre coefficient/Gram API, the eleven-theorem low-order values leaf,
    and the new 25-declaration generic/up-law finite Gaunt tranche.  The report
    distinguishes the now-formal rational Gaunt integral, product
    linearization, and Gram-entry sums from the still-unformalized Wigner 3j
    identification and factorial closed form, and keeps every remaining
    paper-only boundary explicit.

fabius_rvachev_new_frontiers.pdf
    Current 39-page A4 rendering with embedded/subset fonts, Libertinus prose,
    and no Type 3 fonts. It was rebuilt in exactly three strict passes against
    the updated source and is synchronized with the PDF preflight and checksum
    ledger.

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
    PDF structural, geometry, font, text, build-log, and visual preflight.

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

Current repository rebuild verification
---------------------------------------
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
* The refreshed 20-entry checksum ledger includes all five PNG companions and
  synchronizes the TeX, PDF, README, CORPUS_AUDIT, and pdf_preflight entries.

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
sums.  It does not yet identify those integrals with Wigner 3j symbols or prove
the Wigner factorial form.  Christoffel reconstruction, root results,
quadrature, Pade identification, infinite Jacobi products, and the report's
asymptotic claims remain outside Lean.

"New" means not found in the audited repository snapshot.  It is not a claim
of worldwide priority.
