# Executed evidence

`unit_tests.txt` is the new suite's captured output. `audit.json` and `audit_console.txt` report the independent finite checks. Exhaustive counts include overlapping subfamilies and are not counts of distinct matrices. The two alternate-order width refusals are tested refusals, not successful decompositions or negative answers.

`predecessor_tests.txt` records the **actual delivered predecessor packet's** separate 34-test suite. This is not the current maintained repository test suite.

`benchmark_raw.json` stores all five timing samples per case and method, with the actual Python/platform strings. `benchmark_summary.csv` records medians, optimum, validated width, state counts and predecessor subset counts. `benchmark_table.tex` is generated from that run. Both global and component-factored predecessor enumeration are compared; component factoring preserves source row order. Input validation, optimization, independent replay, passive numerical transport and compact serialization are charged. A source-export step is not present.

`stress.json` records larger connected width-three cases with explicitly constructed supplied decompositions. These queries charge decomposition construction/validation, exact optimization, feasibility replay and compact witness serialization. **They do not charge passive-count transport and do not run the exponential predecessor.** Their times are not directly the same workload as the complete-query table.

`summary_macros.tex` and `stress_table.tex` are produced from executed files by `scripts/summarize_results.py`. Reruns replace the corresponding evidence and change environment-specific times. Read the paper's proof, rather than fit an asymptotic bound to timings.

The local measurements include substantial gains, small-input regressions and changes in the apparent advantage after component factoring. None is a native knot-recognition benchmark.
