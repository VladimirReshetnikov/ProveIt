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
    Final synchronized report source, frozen at 2765 lines after the
    rational-Legendre crosswalk reconciliation.

fabius_rvachev_new_frontiers.pdf
    Final synchronized 38-page post-merge PDF. It was rebuilt in exactly three
    halted pdflatex passes from the 2765-line source and passed structural,
    normalized-text, font, and targeted visual-seam review.

fabius_frontier_experiments.py
    Fully commented exact/high-precision experiment. It computes rational
    moments and low-degree Jacobi data exactly, then computes high-degree data
    using mpmath without sampling the Fabius or up functions.

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
    Five figures in dual format. The delivered PDFs preserve the vector
    originals. The TeX selects the PNG companions, and the synchronized report
    is Type-3-free. All five selected PNG payloads are named and hashed in the
    expanded 20-entry live ledger.

CORPUS_AUDIT.md
    Scope, source strata, nonduplication method, and status boundary.

pdf_preflight.json
    Structural record for the final synchronized PDF.

Numerical publication run
-------------------------
python fabius_frontier_experiments.py \
    --degree 200 --dps 4800 --output .

The run independently checks exact rational output through degree 24.  It
found beta_1 < ... < beta_200 < 1/4.  This finite observation is recorded in
the report as evidence, not as a theorem.

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
the five vector plot PDFs.  Refresh the PNG companions selected by the TeX
source after a production run with:

for figure in jacobi_coefficients pi_approximants pi_product_error \
    scaled_jacobi_deficit zero_quantiles; do
  pdftocairo -png -singlefile -r 300 \
      "figures/${figure}.pdf" "figures/${figure}"
done

Final synchronized artifact verification
----------------------------------------
* The frozen 2765-line source had a clean three-pass pdflatex build with no
  unresolved references or citations, rerun warnings, duplicate labels, or
  overfull boxes.
* PDF preflight: 38 A4 pages, unencrypted, text-based, no warnings; Libertinus
  prose is embedded; all 23 font rows are embedded, including five Libertinus
  rows, with zero Type-3 rows. The earlier ten-row vector-plot baseline is
  absent because the synchronized source selects the five PNG companions.
* Crosswalk seam pages 10--13 and the five plot placements on pages 16, 21,
  27, 27, and 28 were rendered and inspected at full-page resolution.
* Normalized PDF text extraction retained all 51 exact public Lean declaration
  names in the determinant, rational-data, and finite-value crosswalks.
* The final 20-entry payload ledger verifies completely, including synchronized
  source, PDF, README, preflight records, and all five PNG companions selected
  by the TeX. The earlier 15-entry ledger is retained only as a historical
  pre-PNG-tracking milestone.

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

"New" means not found in the audited repository snapshot.  It is not a claim
of worldwide priority.
