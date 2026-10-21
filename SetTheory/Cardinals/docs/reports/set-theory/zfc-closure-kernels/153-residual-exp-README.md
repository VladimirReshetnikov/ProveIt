# Additional encoding experiments

The positive mathematical results and full source/primitive proofs are in
the main theory, encoding, and machine sections. This directory preserves
selected negative experiments with their exact scope.

## A two-adic alternative to Cantor pairing

`two_adic/` supplies a second bijective arithmetic codec,
`P2(a,b) = 2^a(2b+1)-1`, its exact source helpers, 644 helper diagnostics,
and complete source-cost reconstruction. The pair-only, reader-only, and
matched substitutions have DAG costs 214, 217, and 225, respectively,
against 206 for the baseline. The one-sided cases mix codecs and are cost
measurements only. The pairer needs a zero output accumulator; a concrete
dirty-destination witness is included. No full-program calibration or
binary machine is claimed for this experiment.

```bash
python3 -B experiments/two_adic/reproduce.py --output-dir ../two-adic-replay
```

## Reset-state deletion

`drop50/drop50.tm` changes native K219 row 34/0 from `0L50` to `0L75`
and deletes state 50, producing 218 working states. It is **rejected**.
The concrete zero-register `CD1` interface at source path
`11101001001000000`, with one zero spare and zero extra gap, returns to a
clean dispatcher after 662 steps with the wrong program-counter tape.

`drop50/check.py` reconstructs the edit from the pinned table and replays
both the baseline and the rejected table. It compares complete tape
supports, not just state/head pairs. `drop50_counterexample.json` records
the original independent-runtime counterexample in its legacy dispatcher
name 96; the new replay uses native dispatcher 84. The state-name
translation is explicit. No blank reachability is claimed.

```bash
python3 -B experiments/drop50/check.py \
  --baseline219 ../zfc218-replay/dependencies/K219_Construction_2026-10-20 \
  --output ../drop50-replay.json
```

## Local-window and head-displacement searches

The `window_search/` programs explore specific state-merge families.

- `sample_windows64.cpp` runs all 6,167 baseline primitive guards under
  twelve deterministic full register/gap/spare assignments, checking every
  exact entire-tape endpoint. It also records the known 312,617-step blank
  prefix. The radius-20 bank has 890,491 distinct state/window pairs from
  74,004 primitive simulations.
- `window_fold.cpp` uses an inductive blank-window overapproximation at
  radius 7, with old/new local-join bounds 8/24.
- `window_fold64.cpp` uses the finite radius-20 sample bank, with bounds
  16/64. It is a greedy search over row alternatives, with early structural
  filters; it is not an exhaustive search over arbitrary table rewrites.
- `headshift_fold.cpp` permits a two-cell head displacement when incoming
  transition directions can implement it without extra states.
- `headshift_fold1.cpp` additionally changes one retained-state row, with
  local-join bounds 16/64.

The selected complete replay is:

```bash
python3 -B experiments/window_search/reproduce.py \
  --baseline219 ../zfc218-replay/dependencies/K219_Construction_2026-10-20 \
  --output-dir ../zfc218-window-search
```

It compiles with `g++ -O3 -std=c++17`, regenerates the finite sample bank,
and reruns the three larger searches. Supply `--compiler` or `CXX` if
needed. The checked-in receipt and logs are from a fresh replay of these
distributed sources. The sample bank is generated rather than duplicated
in the archive.

| Search | Exact recorded trial count | Hits |
|---|---:|---:|
| Radius-7 overapproximation, ordinary merge | 19,868,875 | 0 |
| Radius-20 finite samples, ordinary merge | 37,848,973 | 0 |
| Radius-20 finite samples, head displacement only | 41,202 | 0 |
| Radius-20 finite samples, displacement plus one rewritten row | 71,856,288 | 0 |

For the displacement-only program, compile `headshift_fold.cpp` and invoke
it with the same argument order as `headshift_fold1.cpp`: table path,
output prefix, radius, and sample-bank path.

The `alt157_*` logs record the same searches after the inherited K220
alternative row 157/1 was applied to K219 (`1L148` to `1L187`). These are
additional recorded diagnostics; the default window-search replay uses
the exact pinned K219 table. `zero_break_summary.json` records a separate
69-source screen of contextually known-zero decrement substitutions.

**None of these searches proves a state lower bound, rules out more general
simulation relations, or establishes an unbounded machine equivalence.**
In particular, finite sample windows are not an inductive invariant.
An accepted edit would still require a full correctness proof; these runs
accepted no edit.
