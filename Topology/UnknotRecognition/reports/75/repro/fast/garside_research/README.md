# Certified cyclic Garside preprocessing

The maintained `fastunknot.cyclic_garside` package adapts report 25's MIT-0
implementation. The delivered source remains unchanged in `../../reports/25`.
The production changes add cooperative budget hooks throughout search and
independent replay, validate resource options, and integrate a checked source
branch into recognition. The group normal form and interval optimizer do not
by themselves decide whether a knot is trivial.

From the `fast` directory:

```sh
python -B -m fastunknot recognize examples/stress_braid5_36.json --garside
python -B -m unittest discover -s tests
python -B garside_research/benchmark_kernel.py --output results/garside_kernel_local.json
python -B garside_research/benchmark_pipeline.py --output results/garside_pipeline_local.json
```

The Python API is `recognize(diagram, use_garside=True, garside_radius=1,
garside_seconds=0.1, garside_max_ticks=100000, garside_max_targets=100000)`.
CLI equivalents are `--garside`, `--garside-radius`, `--garside-seconds`,
`--garside-max-ticks`, and `--garside-max-targets`. The three resource limits
accept `None` through the Python API to remove their respective caps. The global
recognition deadline still applies. The default policy leaves the probe disabled.

Only validated source-braid provenance is eligible. Existing braid, Seifert,
descending and modular Alexander obstructions run first. Jones and the optional
exact Alexander polynomial follow the probe. A verified candidate must
have fewer crossings than the current simplified PD before recognition restarts.
The restart preserves the user's backend and reduction options and records
source-branch evidence separately from the earlier PD move trace. Local budget
exhaustion or allocation failure resumes the existing pipeline; global exhaustion
returns `UNKNOWN`. An invalid certificate is an error, not a knot verdict.

`preprocess` first tries the expanded whole-word normal form, then shares
doubled-prefix arithmetic across cyclic interval searches when needed. The exact
interval optimum is for one pass of disjoint substitutions by words of length at
most the selected radius, not for all braid simplifications. Search equality uses
full classical Garside states. `verify` and `verify_radius` replay elementary
identities without importing the normalizer or optimizer. Increasing the radius
makes the target dictionary exponential in that radius.

The uncapped fixed-radius compressor has polynomial word-operation cost.
Combined with the exact fallback it gives a conditional polynomial preprocessing
plus exponential-in-core-size bound. The article proves a quasi-polynomial bound
for a restricted family of inflated small cores. Neither the bounded production
probe nor this family theorem establishes a general sub-exponential algorithm.
See `../../synthesis/cyclic_garside.tex` for the proofs, counterexamples, resource
contract and complete-recognition measurements.

`benchmark_kernel.py` compares shared algebra with a fair reference that rebuilds
it for every cyclic cut. Both arms use the same arithmetic, solve all cuts, and
produce/replay only the winning certificate. `benchmark_pipeline.py` uses 25 knot
inputs, keeps all normal filters enabled, and compares disabled/control/radius-one/
radius-two policies in seven shuffled paired warm rounds. Fresh input diagrams
are constructed outside timing; proposal search, verification, candidate diagram
construction, and restarted recognition are included. A global `UNKNOWN` gets no
speedup ratio. Source hashes, samples, statuses, stages and repetitions accompany
the results in `../results/cyclic_garside_*_20261008.json`.

The `before_filter_order` result is a historical diagnostic from placing the
probe before modular Alexander. The `after_all_filters` result also moved Jones
before the probe, losing the useful gains on inflated unknots. These two
experiments motivated the final placement between modular Alexander and Jones;
each has its own source hashes. Neither measures the final implementation. The archive audit, 47-test log and formerly unexecuted adapter
smoke are in `../../synthesis/data/cyclic-garside-*`; the integrated log records
the complete maintained suite. The 60 small-closure homology comparisons and
resource/restart regressions are in `../tests/test_cyclic_garside_production.py`.
