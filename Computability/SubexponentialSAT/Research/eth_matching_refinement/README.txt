MATCHING PACKING AND THIN PRECISION GAPS
Research refinement for Vladimir Reshetnikov, 27 October 2026

Start with report.pdf. The editable source is report.tex.

RESULT
The new exact-rational matching-potential packing argument reduces the
label-class condition from D_arr^2 * Delta to D_arr * Delta, up to
polylogarithmic slack. Thin additive precision gaps allow larger retained
interpolation ranges. Together with the existing exact Hermite precision
and factorial Cauchy modes, they yield normalized contraction coefficient
94.74820225953415 in the base-two s/sqrt(log2 s) exponent (root M<=s).
The matching comparison combines previous explicit bounds to 374.37762438.
These are upper-bound coefficients, NOT measured runtime ratios.

IMPORTANT LIMITS
There is NO improvement of the unrestricted big-O logarithmic exponent.
This does NOT establish superiority over the independent Claude/Anthropic
algorithm, whose constants are unspecified. The original contraction and
reduction arguments and existing Cauchy-mode lemmas are inherited inputs.
The new proof is ordinary mathematics, not a Lean or other kernel certificate.
The code is a set of exact finite component routines, NOT a full SAT solver.
The theoretical thresholds are enormous; no practical speedup is claimed.

COMPARISON SNAPSHOT
VladimirReshetnikov/ProveIt commit:
770edf7756d197e8b18c26e71ada0c5c11faffd4
Current topic: Computability/SubexponentialSAT
Seven refinement packets and the separate Claude manuscript are compared.
A late summary-only README commit 45233238aebf was also reviewed.
The inherited OpenAI preprint is pinned at:
7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a
Eleven inspected text snapshots and exact Git blob/SHA-256 identities are in
sources/. They are evidence, not scripts to run. No upstream code is executed.

REPRODUCE
Python 3.10+ and its standard library suffice:
  python3 code/verify.py /tmp/eth-normal.json
  python3 -O code/verify.py /tmp/eth-optimized.json
  python3 qa/independent_code_checks.py /tmp/eth-independent.json
  python3 -O qa/independent_code_checks.py /tmp/eth-independent-opt.json
  python3 code/verify_bundle.py
  python3 code/replay_archive.py PATH_TO_RELEASE.zip /tmp/eth-replay.json
On Windows substitute python and a suitable temporary output path.

The checks cover exact conditional expectations, small multigraph labeling,
rigorous logarithm intervals, exact integer schedules, inherited Hermite
losses, weighted tuple counts, and negative controls. Schedule basic_guard
only tests U>0 and minimum u>=2; it is NOT a complete finite contraction guard.

REBUILD PDF
With pdflatex and the packages listed in report.tex installed:
  sh build_report.sh
The helper does not download or install software.

CONTENTS
  report.tex / report.pdf        Mathematical report and compiled PDF
  code/refinement.py            Exact reference component routines
  code/verify.py                Finite checks, with optimization-safe tests
  code/verify_bundle.py         Sealed-file integrity verification
  results/normal.json           Executed ordinary Python check results
  results/optimized.json        Executed optimized Python check results
  sources/manifest.json         Pinned source identity and provenance
  qa/                           Independent code and PDF review records
  SHA256SUMS                    Hashes of all other packaged files

No files, branches, issues, or pull requests were published to GitHub.
