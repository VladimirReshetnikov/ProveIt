PAIRWISE CERTIFICATES FOR ADAPTIVE SAT CONTRACTION
Prepared for Vladimir Reshetnikov, October 26, 2026 (Pacific date)

Read report.pdf, or build it from report.tex and sections/.

MAIN RESULT

The new weighted norm-coupled pair-support certificate improves the explicit
generic cached time/space upper-bound coefficient to

  C = (pi/ln 2) sqrt(15952347164548384057 / 368725000000000000)
    = 29.81160894538347...

Both resources are bounded by
  poly(s+L) * 2^((C+o(1)) s/sqrt(ceil(log2 s))),
under the normalized Boolean tensor-network premises in Section 2.
The eventual safe coefficient is 29.812. The comparable previous coefficients
were approximately 30.891019 for time and 30.753913 for space. The new cached
algorithm uses subexponential space.

For maximum initial degree <= ceil(s^(1/12)), the separate streamed schedule
32 -> 16 -> 8 -> 4 improves the polynomial-space time coefficient from about
23.666169 to 16.81223380188329..., with eventual safe value 16.813.
The generic polynomial-space coefficient 46.184846 is retained unchanged.

These coefficients are per normalized wire, not per SAT variable. The report
includes a conservative explicit bounded-density CNF translation.

There is NO improved unrestricted logarithmic exponent order here. The
existing worst-case SAT order n log log n / sqrt(log n) remains. We do obtain
two new structural obstructions: optimality of the flag coefficient over all
binary separator trees in its entropy model, and a finite rank obstruction
to thinner graded spaces in the four-energy crossing interface.

REVIEW SCOPE AND PINS

Mathematical corpus: all 29 refinement-packet summaries and their source
inventory at ProveIt a7ae5ab55f9627f5af7bf77443b3c34ef8ef1be4.
Detailed proof review focuses on the frontier and shared dependencies.
Closing repository head: 7de9d09fecd17de776d712835ecb2011205c531d.
Its only changes are the public Anthropic formalization links in two READMEs.
The research packets are unchanged. docs/incoming contains its README after
the round-four placement.

User-supplied Anthropic PR #31:
  head 1a6eee293b9e00cb432eef6018a21f523623a9af
  merge 16a5ce41304fcdaea4e0be7c132e1c361dc26da5
The 49-page public paper, endpoint definitions, proof entry points, project
documentation, PaperIndex, comparator and toolchain were inspected. The new
paper is a different revision from the older PDF in ProveIt. No fresh Lean,
nanoda, Comparator, or transitive kernel build was run for this packet.

REPRODUCTION

From this directory, with Python 3.10 or later:

  python3 code/run_checks.py

Only the Python standard library is used. Each checker runs normally and
under python -O; the runner verifies that the JSON outputs are identical.
Failed checks raise explicit exceptions, so optimization cannot disable them.

This regenerates:
  results/cached_checks.json
  results/streamed_checks.json
  results/rank_window_checks.json
  results/verification_summary.json

The cached checker reconstructs all 648 integer supports, checks 186,624
weighted support pairs, replays the inherited 13/7-group certificates, and
certifies the schedule and all branch comparisons using rational intervals.
The streamed checker verifies finite separator recurrences through 128 and
the low-degree coefficient. The rank checker tests both crossing flattenings,
valid modular reconstructions, and insufficient-precision negative controls.

To compile the PDF with an ordinary TeX Live/pdfLaTeX installation:

  bash build.sh

The script makes three passes to stabilize references and contents. It uses
standard packages listed in report.tex. All TeX inputs are included. A full
source-repository checkout or numerical optimizer is unnecessary.

CONTENTS

  report.pdf / report.tex        Complete research report and main source.
  sections/                     All mathematical sections and references.
  code/                         Standalone exact proof checkers.
  data/certificate.json         Fixed plans, weights, and schedule parameters.
  results/                      Replay results and compilation logs.
  provenance/                   Reviewed commits and source Git blob metadata.
  PROOF_STATUS.json             Explicit new/imported/open result boundaries.
  INTEGRATION.txt               Suggested repository placement and index entry.
  SHA256SUMS                    Integrity hashes of delivered files except itself.

VERIFICATION LIMITS

The finite support inequality, separator obstruction, and rank obstruction
are proved in the report. The full contraction consequences import the exact
deformation, recovery, packing, and mode-counting interface, plus published
matrix multiplication algorithms and their ring bridge. The Python programs
verify the new finite certificates and arithmetic; they are not a SAT solver,
a matrix multiplication implementation, or a replacement for the symbolic
proofs and imported dependencies. No practical SAT speedup was measured.

Rebuilding the PDF changes its metadata and therefore its integrity hash.
The provenance source blob identifiers describe the imported repository
objects; they are distinct from the delivered-file hashes in SHA256SUMS.
