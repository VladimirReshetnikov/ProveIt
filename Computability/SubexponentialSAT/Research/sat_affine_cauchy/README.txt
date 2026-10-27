AFFINE GEOMETRY AND FAST CAUCHY TRANSFORMS FOR SUBEXPONENTIAL SAT
Research prepared for Vladimir Reshetnikov -- October 26, 2026 (Pacific)

START HERE
==========
report.pdf is the complete mathematical report. report.tex and sections/*.tex
are the complete editable LaTeX sources. No upstream manuscripts are embedded;
immutable source links and hashes are supplied instead.

RESULT
======
Under the same imported generic normalized-wire contraction interface as the
best existing cached proposal, the new algorithm has bounds

  time:  poly(s + L) * 2^((30.413348726348439... + o(1))*s/sqrt(ceil(log2(s))))
  space: poly(s + L) * 2^((29.466030256594790... + o(1))*s/sqrt(ceil(log2(s))))

The previous best displayed generic cached constants in the inspected corpus
were 30.891018920366092... (time) and 30.753912832054975... (space).
The change is a strict improvement of the proved upper-bound coefficient.
It does not change the unrestricted logarithmic order, establish a finite-size
crossover, or give a measured end-to-end SAT speedup. It uses subexponential
space and does not replace the best polynomial-space guarantee.

The new construction uses the four parallel classes of F_3^2, thirteen cyclic
ordered plans, a pairwise-correlation inequality, and a fully charged
9 -> 13 -> 9 -> 6 -> 6 -> ... recursion. All child entry costs are included.

A separate result gives guarded fast applications of the normalized Cauchy
feature matrix. For odd interpolation nodes it reduces to one convolution.
The scalar implementation is exact; the general product-tree prototype is
slower than the quadratic reference at the small benchmark sizes. These
negative measurements are retained. The odd-node specialization is faster
on all five included matched measurements.

The report also incorporates the user-supplied Anthropic formalization,
analyzes a potential composition, states a precise conditional growth-rate
route, and proves an obstruction to the immediate sparse-oscillator attempt.
No smaller-order SAT algorithm is claimed from that conditional route.

SOURCE SNAPSHOTS
================
Mathematical corpus:
  VladimirReshetnikov/ProveIt
  a7ae5ab55f9627f5af7bf77443b3c34ef8ef1be4
Final follow-up reviewed (README links the Anthropic proof, no new packet):
  7de9d09fecd17de776d712835ecb2011205c531d
Anthropic PR 31 revision explicitly supplied by the user:
  anthropics/formal-math
  1a6eee293b9e00cb432eef6018a21f523623a9af

All 29 refinement packet summaries/status declarations are reviewed; the
interfaces and proofs used in the new comparison receive detailed examination.
The report does not claim an independent proof of every packet. The Lean
development was inspected but not rebuilt or kernel-replayed in this work.

REPRODUCE
=========
Run from this extracted directory, using Python 3.10 or newer:

  python3 code/check_manifest.py
  python3 code/run_checks.py

The hash check should be run BEFORE regenerating files. Rebuilding the PDF
or figures can change bytes even if the mathematical content is unchanged.
All mathematical checkers use only the Python standard library. run_checks.py
runs normal and -O modes, compares their parsed JSON, compares the result with
the delivered reference, and stores both versions under results/.

To rebuild the PDF (pdfLaTeX and the packages named in report.tex required):

  python3 code/build_report.py

The figure is supplied. To recreate it (Matplotlib required):

  python3 code/make_figures.py

To collect fresh local timings (optional; machine-dependent):

  python3 code/fast_cauchy_transform.py --benchmark --output results/local_timings.json

CHECKER MAP
===========
code/certify_four_stage.py
  Final exact menu certificates, rational packing gates, interval arithmetic
  and four-branch recurrence constants. Imports certify_affine_cyclic.py.
code/certify_affine_cyclic.py
  Menu construction and exact dot products. Its standalone entry point also
  checks an earlier conservative 9 -> 13 -> 7 schedule; that schedule is not
  the final result advertised above.
code/independent_fourstage_audit.py
  Independent bit-set construction and rational gate audit; independent
  floating-point recurrence unrolling is supplemental to the exact proof.
code/independent_menu_audit.py
  Independent audit of the common menus and conservative three-stage version.
code/verify_regrouping.py
  Literal enumeration versus exact boundary-table regrouping over a ring with
  zero divisors, exact selector scores, and counted singleton entry calls.
code/fast_cauchy_transform.py
  General guarded synthesis/transpose and odd-node convolution; independent
  rational references, recurrence tests, adjoint tests and optional benchmarks.

SCOPE
=====
This archive contains a mathematical refinement and exact local prototypes,
not an end-to-end SAT solver or a Lean formalization. The fast matrix backend,
the existing deformation/interpolation framework and SAT reductions are
explicit dependencies. PROOF_STATUS.json separates these from the new proofs,
finite computations, source-inspection findings and conditional targets.

provenance/source_manifest.json records immutable paths, Git blob IDs, sizes
and SHA-256 hashes for the available source snapshot files. Hash coverage is
not a claim of line-by-line review of every file. reviewed_commits.txt and
final_documentation_update.patch record the relevant recent history.
MANIFEST.sha256 covers the delivered files other than itself.
