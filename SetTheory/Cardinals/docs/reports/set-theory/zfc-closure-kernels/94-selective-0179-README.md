# Trace-aware grammar search and literal recovery

The searches use independent closed halt-free source atoms. The strict
relation has 162 unordered pairs; allowing shared increments when neither
fragment writes a register tested by the other gives 211 pairs.
`../theory_work/trace_commutation.tex` proves the partial-map criterion.
`check_trace_grammar.py` independently derives footprints and checks exact
trace-normalization witnesses, orientation, routes, reachability and source bounds.

The two retained searches each stop at 128 grammar states. The read/write
incumbent has source depth 47. `literalize_trace_grammar.py` additionally
checks that every retained original word recovers its exact literal spelling.
The unchanged pinned routing compiler verifies the resulting source control
with a register-program bisimulation. Its complete 245-state table and
runtime certificates are in `../variant245/`.

For individual checks, first extract `../reference/zfc245-proof-20261018.zip`
and set `REFERENCE` below to the absolute extracted directory. The root
`code/verify.py` handles that automatically for integrated verification.

```sh
python3 -B check_trace_grammar.py best_strict.json --strict --reference REFERENCE
python3 -B check_trace_grammar.py best_readwrite.json --reference REFERENCE
python3 -B literalize_trace_grammar.py --reference REFERENCE --output FRESH_GRAMMAR.json
```

The search sources are adapted from the attributed baseline
`anneal_routes_zero6.cpp`. Their generation is reproducible and does not edit
the reference. To create fresh sources and restart inputs:

```sh
python3 -B prepare_trace_search.py --reference REFERENCE \
  --criterion disjoint --output-directory FRESH_DIRECTORY
python3 -B prepare_trace_search.py --reference REFERENCE \
  --criterion readwrite --output-directory FRESH_DIRECTORY
```

Compile with `g++ -O3 -std=c++17`. Each search command takes the original
`route-grammar.txt`, `route-constraints.txt`, a fresh output JSON, seconds,
seed, target rule count, `bootstrap-lock54.txt`, and `resume245.txt`, in
that order. Inputs except the resume file live under
`REFERENCE/inputs/state_reduction/`.

| Source | Seconds | Seed | Target | Retained proposals |
| --- | ---: | ---: | ---: | ---: |
| `anneal_trace_disjoint.cpp` | 420 | 445127 | 127 | 4,223,535 |
| `anneal_trace_readwrite.cpp` | 600 | 445211 | 127 | 6,079,246 |

The sources generated from the pinned reference are byte-identical to those
used for the retained runs. Timed proposal counts depend on hardware/load.
Abstract search JSONs inherit an old `framework_states=118` metadata field;
the final shortened framework actually has 117 states. Only a complete
compiled transition table determines the machine count.

`verify_variant_frames.py` is the baseline independent frame checker with
only the two fixed table hashes and the expected depth changed, plus its
docstring. The exact source diff is supplied. All its original obligations
remain. The top-level verifier separately rederives actual-table macro
induction contracts and runs all 8,391 guarded symbolic cases.

