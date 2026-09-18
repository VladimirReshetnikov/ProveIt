# Measurement and fixture provenance

`comparison.json` and `comparison.csv` were generated on 2026-09-18 by
`tools/benchmark.py --repeats 3 --timeout 30`. Successful groups have three fresh
processes; censored groups stop after one attempt. The timer excludes process
creation, imports, JSON parsing and initial Diagram validation. The new raw
scanner additionally revalidates internally; that extra safety cost is counted.
The main run was sequential. CPU: AMD EPYC 9V74 80-Core Processor; container
reported five logical CPUs. Full Python/platform data are in the JSON file.

`ablation.json` uses `tools/ablate.py --repeats 3 --timeout 10` and isolates
stack versus minfill pivots with the same new cached algebra and order routine.
It does not compare an uncached old algorithm with a cached new one.

`stress_validation.json` uses `tools/validate_stress.py`: scans the raw 36-crossing
input and its 24-crossing result after six R2 moves, both with d^2 checks, then
compares rank and full raw homological degrees with the R2 shift. This is an
invariance check of one implementation, not independent large homology software.
The determinant agreement is recorded only as an additional sanity check.

`tests.log` records the final 48 successful test methods (8.538 seconds).
`baseline_tests.log` records the original 19 tests against the original source.
After the main timing run, source hardening added only rejection of invalid
`tries`/verification-time arguments and clarified comments; all valid measured
algorithm paths are unchanged. The worker gained an optional pivot-selection
argument solely for the ablation; its default remains minfill.

`comparison_validation.json` records equality of status, rank/degree maps or
chosen orders for all completed baseline/new pairs. It also records a byte-level
check that the included baseline Python sources equal the supplied original
sources, and a check that regenerating all fixtures preserves their exact
normalized PDs. No checksum files are needed.

The random `four_braid_41.json` and `five_braid_36.json` braid words come exactly
from the corresponding records of the supplied `fast/results/benchmark.json`,
retained here as `baseline/results/benchmark.json`. That older record used
Python 3.14.4 on Windows 11; its 600-second timeout on the 36-crossing raw scan
is historical context, **not** a same-machine speed comparison.

`tools/make_inputs.py` reads those retained source words and constructs the
remaining inputs deterministically: visible sums of the supplied Conway/trefoil
fixtures, and closures of sigma_1...sigma_n with n+1 braid strands. The same
script regenerates the 24-crossing R2-reduced stress PD. No external census or
network data is needed. Named knot identifications are those of the supplied
fixtures; algorithms use their actual PD data, not the names.

Tables in the PDF come from these records. Re-running them on different hardware
will not reproduce exact wall times. Table regeneration does not automatically
update the report's prose; update textual numerical observations separately.
