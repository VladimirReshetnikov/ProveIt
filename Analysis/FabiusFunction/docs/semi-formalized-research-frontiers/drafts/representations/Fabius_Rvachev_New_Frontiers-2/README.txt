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
    Complete 2579-line A4/Libertinus LaTeX report. The merged source adds the
    current scalar-base-change Gram--Stieltjes, all-degree rational native
    Jacobi, and generic/Legendre Gram-determinant Lean boundaries and is
    synchronized with the 36-page PDF below.

fabius_rvachev_new_frontiers.pdf
    Rendered and visually inspected PDF.

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
    originals; the report embeds the PNG companions so the Type 3 DejaVu
    fonts in the vector plots do not propagate into the report PDF.

CORPUS_AUDIT.md
    Scope, source strata, nonduplication method, and status boundary.

pdf_preflight.json
    PDF structural preflight, refreshed after the repository rebuild.

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

After the rebuild, verify A4 page geometry, embedded/subset fonts, a positive
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

Arrival verification performed
------------------------------
* Clean latexmk build with no unresolved references, duplicate labels, or
  overfull boxes.
* PDF preflight: 36 pages, unencrypted, text-based, no warnings.
* All 36 pages rendered to PNG and visually inspected in contact sheets;
  representative plot and table pages were also checked at full render size.
* Python byte-compilation and an independent degree-24 smoke run succeeded.

Repository rebuild verification
-------------------------------
* Exactly three strict pdflatex passes after the source and figure repair.
* 36 A4 pages; Libertinus present; every font embedded and subset; no Type 3.
* No overfull box, TeX error, unresolved reference, citation, or rerun request.
* The live 20-entry checksum ledger includes all five PNG companions.

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
