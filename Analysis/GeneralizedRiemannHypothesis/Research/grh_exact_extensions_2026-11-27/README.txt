EXACT EXTENSIONS OF THE GRH RESEARCH PROGRAMME
Smith normal forms at every precision and optimal graph couplings of zeros
Research report based on the supplied ProveIt repository, 27 November 2026.

START HERE
  paper.pdf       Complete report and proofs.
  paper.tex       Main LaTeX source (inputs the other top-level .tex files).
  FORMALIZATION.txt  Precise formalization targets; no new Lean proof is claimed.
  PROVENANCE.txt     Source mapping, revisions, and verification boundaries.

MAIN CONTRIBUTIONS
1. For a nondegenerate symplectic frame projected onto a Lagrangian block
   over any complete DVR with finite residue field, the full Smith normal
   form has, conditional on feasible residue-field nullity, exactly the
   independent-entry conditional law at every precision.
   The exact cokernel-testing distance is independent of precision.
2. Full matrix entries still expose a persistent alternating-pairing
   obstruction. We compute its entire precision hierarchy and prove
   sharp exponent five, plus an explicit dimension/precision bound.
3. For the Article's rooted-forest zero coupling, we solve the fixed-budget
   graph minimax problem for every Wasserstein exponent p in [1,infinity].
   The largest-displacement optimum has weights proportional to d_i*d_j.
   The proof includes uniqueness, feasibility and mean-error stability.

All three mathematical statements are unconditional. Dirichlet GRH supplies
the application of the graph theorem to finite packets of zero ordinates.
The source theorem is inspected, not independently rebuilt in this task.
The new results have complete human-readable proofs and executable checks;
they are not Lean-kernel-verified.

REPRODUCE THE PDF
Run in this directory:
  pdflatex -interaction=nonstopmode -halt-on-error paper.tex
  pdflatex -interaction=nonstopmode -halt-on-error paper.tex

No BibTeX run is needed: references.tex contains the bibliography.
The already-generated tables and figure are included.

REPRODUCE THE EXACT CHECKS
Python 3 standard library only:
  python3 code/verify_exact.py

Exact graph symbolic certificates and numerical diagnostics require
SymPy and NumPy:
  python3 code/verify_graph_minimax.py --output results/graph_verification.json

The independent graph diagnostic requires NumPy:
  python3 code/independent_graph_check.py

Recreate exact rational tables/certificates and the figure:
  python3 code/make_tables.py
The exact arithmetic uses only the standard library. The figure uses
Matplotlib. This script deliberately raises Python's integer-to-string
digit limit to serialize the large exact rational interval endpoints.

CONTENTS
  code/                Executable formulas and independent checks.
  results/             Exact rational certificates and diagnostic results.
  figures/             Reproducible vector PDF and PNG scientific figure.
  verification/        Source-contract and separate mathematical reviews.
  source_excerpt/grh/  Sixteen unchanged selected upstream source files,
                       including LICENSE and NOTICE.
  source_excerpt/      Pinned source manifests and SHA identities.

The selected Lean files are a source-audit subset, not a buildable
transitive dependency closure. Follow the full upstream README to build
the original proof with its pinned Lean and Mathlib versions.

PROVENANCE
  ProveIt: 3d8689ceae76501a5c50f67da37e85369aac4fb6
  grh-lean: 72fead102f663d5c7a407964a13dc0cf9d977207
  The article sections spn.tex and zer.tex are the direct starting points.

PRIORITY
The extensions are new relative to the inspected Article. Targeted
primary-literature searches did not identify the combined statements.
Worldwide publication priority has not been certified. Classical
finite-field rank laws, Smith distributions, matrix perturbation
inequalities, fractional Laplacians and resistance optimization are
credited in the report.

INTEGRITY
SHA256SUMS.txt lists every deliverable file except itself.
The archive is self-contained for rebuilding the PDF and rerunning checks
after the stated ordinary dependencies are installed.
