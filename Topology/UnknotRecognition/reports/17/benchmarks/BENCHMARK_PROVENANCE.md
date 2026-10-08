# Benchmark provenance and interpretation

## Supplied-order filter kernels

`potts_benchmark.json` records 3,045 completed timed calls: 29 inputs, 15
rotated rounds, and seven arms. The inputs are all 14 named fixtures, the
first 12 accepted five-strand braid closures and shuffled crossing orders
from seed 764259, and the three weaving collision controls W(3,5), W(3,7),
and W(3,11). The benchmark saves every input and order.

The matching arms in this experiment deliberately evaluate at the same
modular A as the five-color Potts implementation. This isolates two ways to
evaluate the same specialization. Exact six-color arithmetic is a separate
specialization with separately recorded detection outcomes. All calls use
fresh uncached Diagram objects and a common supplied order. Construction,
validation, order search, imports, and serialization are outside this kernel
timing region. A second matching call in every round supplies the A/A control.

The source SHA-256 dictionaries recorded before and after this experiment
agree. Two source files were subsequently changed to encode exact witnesses
as signed hexadecimal strings: `potts_exact.py` and
`potts_factorized_exact.py`. The raw evaluators and their arithmetic helpers
were unchanged. Those edits prevent Python's decimal integer conversion
ceiling from breaking JSON output for long inputs. Recognizer and CLI
integration was also completed after the kernel measurements; those entry
points were not part of that experiment.

The exact measured versions of all eight recorded modules are available in
`measured_source/fastunknot/`. The two earlier wrapper versions were
reconstructed by undoing only the known serialization edits; **each entire
reconstructed file was required to match its original recorded SHA-256**.
`benchmark_source_audit.json` records that verification and the AST hashes
of every unchanged top-level function. Only `potts_exact_obstruction` and
`factorized_potts_exact_obstruction` changed; `witness_from_exact` was added.
`post_benchmark_wrapper_changes.patch` is the complete source difference.
The measured-source directory is an eight-module provenance snapshot, not a
standalone recognizer checkout.

## Normal recognition pipeline

`pipeline_benchmark.json` and `.csv` record 476 completed timed calls: all
14 fixtures plus the three weaving controls, seven rotated rounds, and
matching A/A, exact six-color, and factored exact six-color arms. Here the
matching backend uses its native generic A. All ordinary preprocessing and
recognition stages remain enabled. The timed region includes JSON parsing,
checked Diagram conversion/validation, recognition, and JSON result encoding.
Imports, file I/O, CLI argument parsing, and process startup are excluded.
This is an experiment in a hot process, not a cold CLI startup comparison.

All 476 verdicts were consistent and complete, and source hashes agreed
before and after the run. Only five inputs reached Jones evaluation:
Conway, Kinoshita–Terasaka, and the connected sums of two, three, and eight
Conway diagrams. The other 12 inputs were decided earlier, including all
three weaving controls. Backend speed claims are explicitly suppressed for
those bypassed inputs. The five exercised cases had wide timing intervals
and A/A variation, so this seven-round run supports **no full-pipeline
speedup claim**.

The two experiments answer different questions. Exact agreement and reduced
state/transition counts establish the implementation effects independently
of wall-clock noise. The recorded per-input timing intervals are local
measurements on this corpus, not a uniform speed guarantee or a claim about
the distribution of knots. `potts_summary.csv` preserves every kernel case,
including substantial regressions. `factorization_proof_notes.tex` gives
the parameterized complexity argument separately from these measurements.
