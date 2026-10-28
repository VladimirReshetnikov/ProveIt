A DENSITY-SENSITIVE REFINEMENT OF EXACT #k-SAT COUNTING
Research note prepared for Vladimir Reshetnikov, 26 October 2026.

MAIN RESULT
For fixed k and A, a formula with n variables and at most B*n clauses,
1 <= B <= (log n)^A, admits deterministic exact counting in

  poly(n,m) * 2^{ O( n*log(2+B)/sqrt(log n) ) }

time and polynomial space, using the cited preprint's tensor contraction
theorem. At B = Theta(log log n), the exponent numerator improves from
n*log log n to n*log log log n. The unrestricted worst-case exponent is
unchanged. The result is a refinement of a proved upper bound, not an
actual-runtime comparison or a claim of independent verification of the
entire upstream preprint.

ARCHIVE CONTENTS
  report.pdf                     The complete research note
  report.tex                     Self-contained LaTeX source
  checks/density_checks.py       Exact component checks and optional
                                  small-graph numerical diagnostics
  checks/check_retuning.py       Exact Hermite multiplicity/precision checks
  checks/check_smith.py          Exact rational Cauchy-minor valuation checks
  results/*.json                Outputs from the delivered scripts
  source_manifest.json           Pinned upstream commit, paths, blob hashes,
                                  SHA-256 digests, and source locations
  fetch_sources.py               Optional verified download of pinned sources
  build_report.py                Rebuild the PDF with pdflatex
  run_checks.py                  Rerun all validation scripts
  integration_notes.txt          Specific upstream points to change
  LICENSE-UPSTREAM.txt           The upstream repository's Apache 2.0 license
  SHA256SUMS                     Integrity hashes of all other archive files

REPRODUCE THE CHECKS
From the archive directory, run:
  python3 run_checks.py

Python 3.10 or later is recommended. The checks require only the standard
library. NumPy, if present, adds optional floating-point spectral diagnostics;
the general expander theorem is a cited mathematical input, not established
by these diagnostics.

The scripts test:
  * 11 exact rational density-parameter cases;
  * 7 small Margulis--Gabber--Galil graphs;
  * 4 exhaustive toy Tanner-distance/shortening cases;
  * 2 greedy parity-selection examples using a brute-force oracle;
  * 364 Hermite parameter cases, 33,566 interpolation nodes, and
    434,996 coefficient-error inequalities;
  * 5,072 exact minors of 24 Cauchy matrices of sizes up to 6 by 6.

These finite checks supplement the proofs. They are not the complete fast
SAT algorithm, a proof-assistant formalization, or a practical performance
benchmark. The toy Tanner examples use manageable local codes, not the
enormous conservative parameters of the asymptotic construction.

REBUILD THE REPORT
Install a LaTeX distribution containing pdflatex and the standard packages
listed in report.tex, then run:
  python3 build_report.py

The script runs pdflatex three times in build/ and copies the finished PDF
to report.pdf. It does not download or install software.

PINNED UPSTREAM MATERIAL
The analysis uses openai/math commit:
  42907c9e999cc00d6abe7a50bfc1023250edd1b9

The source preprint is "The Exponential Time Hypothesis is False", revised
25 October 2026. Its four TeX files were retrieved and their Git blob hashes
verified. Upstream files are not redistributed in this archive.
To fetch and verify those files when network access is available, run:
  python3 fetch_sources.py --destination upstream

No GitHub files, branches, issues, or pull requests were changed.

SCOPE OF THE ADDITIONAL RESULTS
The report also proves smaller Hermite precision budgets and permits a
larger retained-level parameter. The matched leading upper-bound coefficient
for mode enumeration decreases by a factor of sixteen. This is not a
sixteen-fold measured speedup and does not change the sqrt(log n) denominator.
The sharper Max-k-SAT approximation corollary is already implicit in the
source's fixed-density theorem and is identified as such.

All new assertions are presented as a research note with explicit hypotheses
and proofs. Broader novelty or independent publication priority is not claimed.

