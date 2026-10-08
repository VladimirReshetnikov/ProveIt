# Recorded results

`benchmark.json` contains interpreter/platform metadata, every input braid and
converted PD code, the selected crossing order, per-mode summaries, and all 54
raw measurements (6 inputs × 3 modes × 3 repetitions). `benchmark_raw.csv`
contains the same raw timing records in tabular form. The three modes are full
homology, one low window of depth two, and a two-sided decision probe of depth
two. The single-window and full outputs deliberately contain different amounts
of information.

The ratios in `benchmark_table.tex` are medians of paired full/window ratios.
They are not production-pipeline speedups. Every displayed timing completed;
the preliminary pilot was not used in the published table.

`validation.json` is an independently seeded audit of 100 cube cases with 393
low-window comparisons, 1,772 certified nice stages, and 15 padding checks.
Inputs, full expected homology ranks, and adaptive verdicts are stored.

`unittest.log` records the initial 14-method successful suite run (8.800 s).
`unittest-final.log` records the rerun after additional invalid-argument checks
(8.295 s). Runtime variation is not a failure condition.

`cli-unknown.json` and `cli-adaptive.json` record the torus-example smoke tests:
fixed depth zero is UNKNOWN, while an adaptive run rejects it as nontrivial.
`pdf-build.log` records the final LaTeX build diagnostics. Harmless underfull
bibliography boxes are permitted; no unresolved references or overfull boxes
remain.
