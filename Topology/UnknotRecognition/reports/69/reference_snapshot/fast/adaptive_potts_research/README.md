# Adaptive Potts policy control

`initial_policy.py` is the frozen first scheduler, before the polynomial-tail
rule. Its SHA-256 agrees with `fastunknot/adaptive_potts.py` in
`../results/adaptive_potts_initial_20261008.json`. It is a benchmark control,
not a production backend. The final benchmark loads it under the
`fastunknot` package so its relative imports use the maintained exact kernel.
The kernel's source hash is also retained in each result archive.

Run `python -B benchmark_adaptive_potts.py --output results/FILE.json` from
`fast/` to compare the current policy, this control, ordinary exact Potts,
an identical ordinary control and eager separator preparation. The initial
record predates the added 144-crossing grid case and the paired initial-policy
arm. Each archive records its own source hashes and measurement scope.
