# Final completed-run evidence

`unittest.txt`: 47 tests, all passing, on the final lazy-generator implementation.
`audit.json`: deterministic exhaustive and generated finite-algebra audits.
`benchmark.json`: raw paired timings and environment; `compression.csv` and
`genus_scaling.csv` are tabular views of the same measurements.
`examples.json`: five independent example-certificate replays plus a CLI
producer/replayer smoke check. `build_audit.json`: PDF build and visual review.

The benchmark excludes input parsing, geometric source construction, and
independent replay. It is not a native knot-recognition benchmark. The dense
matrix verifier was run on every compressed/literal benchmark case, but not
inside the evaluator's timed interval. The binary comparison is a separate
relator-based genus-scaling family and has both scalar gains and slowdowns.

To reproduce without overwriting this directory, run from the package root:

```sh
python reproduce.py --output-dir results-rerun
```

Timing values need not match. Deterministic finite audit data should match.
The native ProveIt test suite and a proof assistant were not run.
