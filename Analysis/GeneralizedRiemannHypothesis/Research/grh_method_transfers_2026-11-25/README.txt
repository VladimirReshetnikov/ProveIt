BEYOND DIRICHLET GRH -- TRANSFER ANALYSIS
Prepared for Vladimir Reshetnikov, November 25, 2026.

START HERE
  report/report.pdf     Complete research report and proofs.
  report/report.tex     Main LaTeX source (three included section files).

PRINCIPAL FINDINGS
  1. Optimal periodic approximation of Frobenius class functions, with the
     exact nonabelian character obstruction for every finite Galois group.
  2. A one-sided, centering-free, finite-sum criterion for Dedekind RH on
     fourth-power checkpoints; explicit target T^3-T-1, discriminant -23.
  3. The compulsory ramification cost of small normalized Selmer budgets,
     plus a bounded-support refinement extracted from the upstream proof.

CLAIM BOUNDARIES
  No additional open conjecture is proved. The cubic arithmetic bound remains
  open in this analysis. Fourth-power sampling is credited to existing work;
  no literature-priority claim is made for the deductions in this report.
  The source was inspected and matched byte-for-byte with its GitHub inventory.
  No full Lean build or independent kernel replay was run here.
  Formalization files are uncompiled interface specifications/audit commands.
  Numerical cubic values illustrate only a finite range and use floating point.

REPRODUCE
  python3 code/check_models.py
  python3 code/check_source_blobs.py
  python3 code/cubic_checkpoints.py --max-n 20
  python3 code/make_figures.py
  cd report
  latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

DEPENDENCIES
  Mathematical check scripts: Python standard library.
  Figures: NumPy and Matplotlib. Manuscript: pdfLaTeX and latexmk.
  Lean audit: separately obtained pinned grh-lean checkout and Mathlib cache,
  followed by a successful upstream `lake build` before running Audit.lean.

CONTENTS
  code/           Reproducible exact and numerical checks.
  results/        Recorded outputs, source audit, cubic CSV values.
  figures/        Standalone PDF figures and PNG previews.
  formalization/  Uncompiled Lean interface and upstream audit driver.
  evidence/       Source provenance, prior-report comparison, source inventory.
  evidence/upstream/  Selected unmodified source files and upstream licenses.

SOURCE
  https://github.com/lsernau/grh-lean
  commit 72fead102f663d5c7a407964a13dc0cf9d977207
  Upstream source copyright/licensing is preserved in evidence/upstream/.

CHECKSUMS
  SHA256SUMS lists every deliverable in this archive except itself.
  The ZIP is an original deliverable; no GitHub repository was modified.
