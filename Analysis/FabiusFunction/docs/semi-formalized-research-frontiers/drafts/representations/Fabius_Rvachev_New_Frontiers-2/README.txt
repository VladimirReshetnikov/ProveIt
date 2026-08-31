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
    Complete 37-page, 2,668-line LaTeX report.  The semantic merge retains
    the canonical A4/27 mm/Libertinus preamble and incorporates the current
    determinant/rational Lean crosswalk.

fabius_rvachev_new_frontiers.pdf
    Rendered and visually inspected PDF, refreshed after the post-intake
    formal crosswalk.

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

figures/*.pdf
    Five one-page vector figures embedded in the report.  The publication run
    writes embedded, subset CID TrueType fonts; none contains Type 3 fonts or
    raster images.

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
Required: a reasonably complete TeX Live installation with pdflatex.
From this directory:

pdflatex -interaction=nonstopmode -halt-on-error fabius_rvachev_new_frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error fabius_rvachev_new_frontiers.tex
pdflatex -interaction=nonstopmode -halt-on-error fabius_rvachev_new_frontiers.tex

Re-run the numerical experiment
-------------------------------
Required Python packages: mpmath, numpy, matplotlib.

A quick smoke run:

python fabius_frontier_experiments.py \
    --degree 24 --dps 500 --output /tmp/fabius-smoke

A higher target degree requires rapidly increasing precision because the
current monomial-basis recurrence is cancellation-prone.

Verification performed
----------------------
* Clean, exactly three-pass, strict serial pdflatex build from the frozen final
  source.  The third-pass log has no LaTeX or package warnings, unresolved
  references, duplicate labels or destinations, or overfull boxes.  Its nine
  benign underfull notices are confined to the narrow claim-status table on
  page 6, whose readability was checked at full render size.
* PDF preflight: 37 unencrypted A4 pages at 595.276 x 841.890 points, zero
  rotation, and A4 MediaBox/CropBox/BleedBox/TrimBox/ArtBox on every page.
  All 35 font rows are embedded and subset, Libertinus is present, and there
  are no Type 3 or Latin Modern fonts.  The report and all five standalone
  figure PDFs contain vector content and no raster images.
* Layout-preserving text extraction produced 2,248 lines (129,168 bytes).
  Whitespace-normalized text retains all 41 unique public Lean declaration
  names inventoried in the report, including all 18 names in the new
  determinant crosswalk.
* All 37 pages were rendered and visually inspected in four contact sheets.
  Pages 1, 6, 11, 12, 23, 33, and 37 were also checked at 150 dpi; all five
  standalone figure PDFs were inspected together at full plot scale.
* Python byte-compilation was rechecked.  The numerical program, CSV files,
  figure PDFs, and publication log are byte-identical to the audited local
  publication run, whose independent degree-24 smoke output matched the
  publication exact-low-degree CSV byte for byte.

Claim status
------------
The report distinguishes:
* results already present in the audited repository;
* new proofs or finite identities developed in the report;
* applications of classical external OPRL/Christoffel/Padé theorems after
  verifying their hypotheses for the up-law;
* high-precision observations; and
* explicitly labeled conjectures.

"New" means not found in the audited repository snapshot.  It is not a claim
of worldwide priority.
