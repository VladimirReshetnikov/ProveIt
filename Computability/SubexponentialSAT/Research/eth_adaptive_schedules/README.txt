ADAPTIVE SCHEDULES AND EXACT INCREMENTAL PACKING
Research prepared for Vladimir Reshetnikov, October 26, 2026 (Pacific time)

MAIN RESULTS
1. A rational multistage polynomial-space schedule has normalized contraction
   exponent coefficient 63.781173756244...; 64 is a safe eventual coefficient.
   The comparable combined fixed-alphabet boundary certificate is about
   66.192723693577. This compares compatible contraction upper bounds.
2. A separately costed cached schedule has time coefficient
   37.591702555541... and space coefficient 33.623040921657...; safe eventual
   coefficients are 37.6 and 34. This route uses subexponential memory.
3. An exact incremental matching-potential kernel preserves the reference's
   entire deterministic output while reducing update work from O(V M Q^3)
   to O(M Q^2 + V Q) rational operations. Initialization, coloring, bit costs
   and added product-table memory are separately charged in the article.
4. A common-denominator integer column kernel preserves all exact candidates.
   It improves the prior cached-suffix implementation in measured examples;
   the already known O(N Q^2) dense arithmetic order is not claimed as new.

SCOPE
The analytic coefficients multiply s/sqrt(log2(s)) for the explicitly stated
normalized Boolean tensor interface, not the number of SAT variables.
The general SAT logarithmic order is unchanged. The proofs retain the supplied
framework's exact algebraic identities and degree/precision interfaces.
The Python code consists of schedule generators and packing kernels, not a
complete SAT solver. The finite checks do not prove the all-size statements.
The reported timings concern synthetic graph-packing inputs in one Python
environment, not end-to-end SAT runtimes or universal speedup guarantees.
The cached and polynomial-space time certificates have different space costs.
See report.pdf / report.tex for the complete hypotheses, comparisons and proofs.

REVIEW SNAPSHOT
Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: d098ba436b33df19365a44dd178694ff52845d19
Seven existing refinement packets plus all eight incoming archives were
reviewed, including ETH_Matching_Packing_Thin_Gaps_2026-10-27.zip.
The exact executable reference files and their original archive member paths
are retained under code/reference/ with source hashes in provenance.json.

REPRODUCE ALL EXACT CHECKS (Python 3.10+; standard library only)
    python3 -B run_checks.py

The runner executes the three checkers normally and with Python -O, compares
the mathematical results to the shipped receipts and to each other, and writes
results/replay.json. Flags, elapsed time and interpreter-version metadata are
the only ignored fields. Any failed check or substantive mismatch exits nonzero.
The shipped check and benchmark records remain unchanged.

The checks include exact schedule coefficient enclosures; 932 column cases
with 9,828 candidate potentials per implementation; 399 matching cases with
1,920 exact trace values; and 128 independent expectation checks derived from
1,366 complete label assignments. Tests do not rely on Python assert statements.

REPRODUCE KERNEL BENCHMARKS
    python3 -B code/benchmark_kernels.py --output results/benchmarks_rerun.json

Five alternating repetitions and all raw timings are recorded. Every timed
output is checked for exact equality. Shipped measurements are retained in
results/benchmarks.json and results/benchmark_summary.csv. Source hashes in the
benchmark record match the delivered implementation files.

GENERATE EXAMPLE PARAMETERS
    python3 -B code/schedules.py 1000000 3 --family polynomial
    python3 -B code/schedules.py 1000000 3 --family cached

The first positional argument is lambda=ceil(log2(s)); s itself is not formed.
Positive taper is not by itself a finite-instance feasibility certificate.
A contractor must still check its packing, degree, precision and fallback gates.

VERIFY THE DELIVERED FILES
    sha256sum -c MANIFEST.sha256

Run this before the replay or rebuild commands, which intentionally replace
their generated outputs. The ZIP also has per-member CRC checks.

BUILD THE PDF
    sh build_report.sh

Requires pdflatex with the standard packages named in report.tex. The script
uses three passes, disables shell escape, compiles in a temporary local build
subdirectory, and copies the completed PDF to report.pdf. A precompiled PDF is
included in the final archive. No network access is used by the scripts.

CONTENTS
    report.tex, report.pdf  Complete article and source
    code/                  Portable kernels, schedule generators and checkers
    code/reference/        Verbatim comparison implementations and provenance
    results/               Exact check receipts and raw benchmark evidence
    run_checks.py          Normal/-O replay and result comparison
    build_report.sh        Reproducible three-pass PDF build
    MANIFEST.sha256        SHA-256 hashes of all other delivered files
    provenance/            Source snapshot, proposal inventory and relocation audit

CLOSING REPOSITORY CHECK
Head 474ddba696a5d385c091c23fb2995f69edd13e00 relocates the same eight incoming packets into Research/. All 211 retained payloads match their reviewed archives by Git blob identity; no new proposal was introduced. See provenance/closing_relocation.json.
