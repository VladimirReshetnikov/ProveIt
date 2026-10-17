# Reproducing the optional research experiments

This directory preserves the search evidence behind the report. It is optional:
the archive's top-level `verify.py` checks the positive 252-state result without
rerunning these searches. None of the negative searches is a lower bound for
all binary Turing machines. A fuel limit, unsupported symbolic configuration,
or rejected proposed register-box contract is not a proof of semantic
inequivalence or nonhalting.

`workspace/` reproduces the original relative layout of the research drivers.
It contains the required data, imported helper modules, complete search
ledgers, and selected emitted tables. Every payload file is an unchanged byte
copy of the research workspace. `packaged_files.json` records those original
paths, byte sizes, SHA-256 values, and experiment groups. `imported_fixtures.json`
records pinned repository paths and Git blob identities; `ATTRIBUTION.md`
explains ownership and the license boundary.

## Environment and working copy

Use Python 3.10 or later, with assertions enabled. The archived runs used
Python 3.12. Do not pass `-O` or set `PYTHONOPTIMIZE`. The C++ bootstrap census
also requires `g++` with C++17 support. There are no Python package or network
dependencies. The optional runs take seconds to minutes each; beam searches
and the large census take longer. Wall-clock limits depend on the host.

Run the following from the extracted archive root. Several original drivers
write results beside themselves, so make a working copy before rerunning them:

```sh
task_experiments=$(mktemp -d /tmp/cachemp252-experiments-XXXXXX)
cp -R experiments/workspace/. "$task_experiments/"
cd "$task_experiments"
mkdir -p rerun
```

Every command below is relative to that working copy. The archived results
remain in the extracted archive. On reruns, elapsed times and recorded output
paths will differ. The beam commands below use the exact archived expansion
counts and a generous time ceiling to reproduce the explored prefixes. The
two-incoming action search is inherently wall-clock bounded and may reach a
different frontier on another host.

Only the custom research drivers listed below should be run directly.
Imported helpers such as `sources/candidate252_independent_audit.py` retain
their original ProveIt-repository main functions and are included for imports.
Their standalone main functions require the larger upstream repository;
they are not entry points for this package.

## 1. Mixed read-row merges, both layouts, and relocated entries

```sh
python3 experiments/mixed_box_search.py --seconds 600 --fuel 1000
python3 experiments/rescreen_entries.py
python3 experiments/mixed_cache_box_search.py --seconds 600 --fuel 1000
python3 experiments/rescreen_cache_entries.py
```

Both layouts completed 14,386 mixed-row recipes. Each run made 1,132,306
literal finite register-box tests and retained 1,821 candidates at that stage.
The first layout used the pinned permutation252 table and 8,391 affine
instruction guards; the second used the new cache-MP table, its Safe physical
layout, and 8,361 guards. The initial screen deliberately set aside relocated
macro entries. The corresponding `rescreen_*` driver finishes those cases
using the explicitly proposed relocated-entry oracle. No recipe survived the
combined screen in either layout.

The four results are `experiments/mixed_box_results.json`,
`relocated_entry_results.json`, `mixed_cache_box_results.json`, and
`relocated_cache_entry_results.json`. Literal box tests are finite samples;
passing them would not supply an unbounded box contract. The later oracle
screen is conditional on the proposed contracts, including their relocated
entry/exit conventions. These limitations apply to the search's conclusion.

## 2. Closed decoder rotations and coordinated beams

```sh
python3 agents/machine_reduction/rotation_search252.py \
  --iterations 3000 --restarts 4 --seed 252 \
  --output rerun/rotation-results.json
python3 agents/machine_reduction/rotation_beam252.py \
  --expansions 314 --seconds 3600 --ceiling 257 \
  --output rerun/rotation-beam-results.json
python3 agents/machine_reduction/rotation_beam252.py \
  --cache-mp --expansions 304 --seconds 3600 --ceiling 257 \
  --output rerun/rotation-cache-beam-results.json
```

The first driver checks all 238 admitted single transformations, followed by
12,000 seeded stochastic mutation attempts. No emitted graph had fewer than
252 working states. Its closed-region condition protects break/continue
semantics; commutation of distinct adjacent increments is also admitted.

The pinned-layout beam costed 54,527 tables in 314 expansions. The cache-MP
beam costed 52,786 tables in 304 expansions. Both original runs used a
480-second ceiling and stopped with a nonempty frontier, with the best
observed cost still 252. The commands above reproduce those expansion
prefixes rather than claiming that the frontiers were exhausted. Increasing
the expansion bounds performs new research. The emitted-state count alone
does not prove an altered table's instruction simulation or blank bootstrap.

## 3. Decoder shape and the zero-run return counter

```sh
python3 agents/machine_reduction/zero_run_search252.py \
  --iterations 6000 --seed 1729 --output rerun/zero-run-search-results.json
```

This is 24,000 mutation attempts: 6,000 at each of four score weights. The
original decoder has 18 leaf paths containing seven consecutive zero edges.
The best sampled reduction in that path count was 10, at a cost of 269 emitted
states. No shorter return-counter candidate was produced. The final
`pareto_by_seven_zero_path_count` ledger and exactly the table/decoder pairs
named by that ledger are included. Superseded intermediate frontier files are
omitted. Shortening the return counter would require a separate full runtime
check; this shape score does not establish that transformation.

## 4. General rotations with control re-encoding and phase no-op erasure

```sh
python3 experiments/control_rebased_rotations.py --cache \
  --output rerun/control-rebased-cache-rotations.json
python3 experiments/erase_phase_noop.py
```

The first driver considers all 331 global single binary rotations of the
203-node cache decoder. It preserves the complete ordered leaf control-flow
graph, including both decrement branches, by re-encoding existing break and
continue operations where possible. Seven emitted tables have 252 states;
five pass the complete conditional affine screen. No table has fewer than
252 states. The five passing table/decoder pairs are retained under
`experiments/control-rebased-candidates/`; no blank initialization has been
proved for them by this search.

The second driver erases the specific transfer occurrence at prefix
`11101001011000110`, assuming the separately computed phase invariant
`X = 0` there. It contracts the leaf graph and checks the remaining successor
identities. The result has 259 states and passes its 8,357 affine guards. Its
table, decoder, and `phase-erased-results.json` are retained as a larger
control. The erasure driver does not prove the phase invariant itself; its
logical dependency is the Safe-root phase analysis in the next section.

## 5. Cache-MP affine checks and ordinary uniform folds

```sh
python3 agents/machine_reduction/check_rotation252.py \
  agents/machine_reduction/rotation-candidates/mp-cache252.json \
  --table agents/machine_reduction/rotation-candidates/mp-cache252.tm \
  --physical 6,2,0,4,3,7,8,5,1 --output rerun/mp-cache252-check.json
python3 agents/machine_reduction/check_rotation252.py \
  agents/machine_reduction/rotation-candidates/mp-cache-permuted252.json \
  --table agents/machine_reduction/rotation-candidates/mp-cache-permuted252.tm \
  --physical 4,5,0,8,6,2,1,7,3 --output rerun/mp-cache-permuted252-check.json
python3 agents/machine_reduction/fold_changed252.py \
  --name mp-cache252 --physical 6,2,0,4,3,7,8,5,1 \
  --output rerun/mp-cache252-uniform-folds.json
python3 agents/machine_reduction/fold_changed252.py \
  --name mp-cache-permuted252 --physical 4,5,0,8,6,2,1,7,3 --start 0 \
  --output rerun/mp-cache-permuted252-uniform-folds.json
```

Both baseline tables pass all 8,361 guards. Each subsequent fold search
completes 55,471 recipes, with zero survivors. The family preserves all 55
arithmetic-box support rows and their targets, and redirects all incoming
transitions of one eligible deleted state to one retained state. Fuel is
1,000 affine rules per guard. The archived checks are ordinary Python
certificates relying on unchanged register-box contracts. The main archive
contains the separate completed source-binding and blank-start arguments.

## 6. Safe-root phase analysis, vector effects, and one-incoming actions

The zero-start phase control can be regenerated directly:

```sh
python3 agents/machine_reduction/cache_phase_analysis.py \
  --output rerun/mp-cache252-phase.json
```

The actual Safe bootstrap has logical primary registers
`[6,0,0,0,2,0,0,0,0]`. The command-line wrapper defaults to nine zeros;
use the explicit register argument to reproduce the actual-root artifact:

```sh
python3 agents/machine_reduction/cache_phase_analysis.py \
  --dag agents/machine_reduction/rotation-candidates/mp-cache-permuted252.json \
  --initial-registers 6,0,0,0,2,0,0,0,0 \
  --output agents/machine_reduction/mp-cache-safe-phase.json
python3 agents/machine_reduction/phase_zero_fold252.py \
  --output rerun/phase-zero-fold-results.json
python3 agents/machine_reduction/vector_effect_fold252.py \
  --output rerun/vector-effect-spare-fold-results.json
python3 agents/machine_reduction/vector_degree1_fullaction252.py
```

The finite abstract domain is `{0,1,at least 2}` in each of nine registers.
Its transfer functions overapproximate all natural values, and its computed
closure retains 8,358 guards. This is an ordinary inductive invariant,
computed and checked by Python, without a local Lean verification of that
implementation.

The phase-zero sweep completes 55,471 uniform-fold recipes. The vector sweep
completes another 55,471 using exact symbolic primary-register vectors,
independently justified zero/positive guards, and arbitrary valid finite spare
suffixes. Neither has a survivor. The latter permits multiple register
excursions when their final primary-register effect agrees, and explicitly
tracks newly appended zero spares. Its optional `--exact-spares` mode is not
the mode used for the archived search.

The final sweep covers 131 eligible states with exactly one external incoming
row. That row may write either bit, move either direction, and target any
remaining working state or halt: 132,048 recipes in all. It completes with
zero survivors, using the same phase/vector/spare relation and unchanged
box-support rows. Its result is
`agents/machine_reduction/vector-degree1-fullaction-results.json`.

## 7. Two-incoming full-action search: explicitly partial

```sh
python3 agents/machine_reduction/cache_context_search.py \
  --dead 252 --seconds 120 --output rerun/cache-context-delete252-fullaction.json
```

This searches the earlier cache-MP physical layout. Deleting old label 252
exposes incoming rows `(249,1)` and `(251,0)`. Each may take any write/direction
combination and any remaining working-state target. The family contains
1,008,016 full assignments. The archived 120-second run rejected 424,182
assignments through its weighted partial-assignment pruning, found no
survivors, and left **583,834 assignments unresolved**. Its full pruning
ledger and remaining frontier are included. The driver records the identity
`planned = pruned + remaining + survivors`; it does not implement a resume
command. Rerunning the command repeats the bounded search, and a different
host may examine a different-length prefix. No conclusion about the
unresolved assignments is warranted.

## 8. Literal cache-MP blank-start permutation census

```sh
python3 agents/proof_audit/cache_boot_census.py \
  --table agents/machine_reduction/rotation-candidates/mp-cache252.tm \
  --permutations agents/proof_audit/mp-cache252-census4096/permutations.txt \
  --limit 1000000 --output-dir rerun/census4096
python3 agents/proof_audit/cache_boot_census.py \
  --table agents/machine_reduction/rotation-candidates/mp-cache252.tm \
  --permutations agents/proof_audit/mp-cache252-census-next12288/permutations.txt \
  --limit 1000000 --output-dir rerun/census-next12288
```

The Python driver compiles the supplied `cache_boot_census.cpp` into each
output directory using `g++ -O3 -std=c++17 -Wall -Wextra`, runs every transition
literally, and independently replays every Safe hit and the first four cases
of each batch in Python from actual blank start 0. No compiled executable is
included in the archive. The 16,384 distinct permutations are identity,
followed by the uninterrupted unique sequence from
`random.Random(20261017).shuffle`. The lists are committed to eliminate any
ambiguity about the sampled domain. A 1,000,000-step limit applies to the
normalized suffix starting in state 1, head 0, with a one at position 1; the
driver separately checks the literal one-move prefix from blank start 0.

The combined outcomes are 14,828 fuel limits, 1,555 halts, and one Safe root.
Fuel limits make no nonhalting claim. Global permutation index 6,895 (local
second-batch index 2,799) yields post-permutation `[0,3,5,6,8,7,4,2,1]` and
logical-to-physical map `[4,5,0,8,6,2,1,7,3]`. After 707,393 actual blank
steps the machine is in old state 96 at head -13, with gap 40, primary
registers `[6,0,0,0,2,0,0,0,0]`, and 295 zero spare blocks. The full-tape
certificate and hit table are included. The latter's SHA-256 is
`9ba862d15e0f689525281e1c96083acf7f389157bd56d6a2676f223106dc07a9`.

The two `results.json` files, `literal.jsonl` files, exact permutation/row
inputs, and the combined `mp-cache252-census16384-summary.json` are retained.
The summary is an aggregation of these two result files, not a third search.
Paths embedded in historical records identify the original research runs;
their files are present at the corresponding relative paths in this workspace.

## 9. Short-gap diagnostic

```sh
python3 agents/proof_audit/short_gap_probe.py \
  --fuel 100000 --output rerun/short_gap_probe.json
```

The driver starts from the pinned table and examines the proposed deletion of
old state 204, redirecting `(172,1)` to action `(1,R,252)`. It checks a literal
15,963-step blank prefix and compares whole binary frames with source steps.
The proposed gap-19 correspondence agrees for the first 17 source operations.
At the following zero decrement, the expected frame is not reached within
the stated 100,000-move fuel, and an earlier dispatcher visit already has a
different frame. The source trace subsequently needs depth 20 while only 19
zero cells were proposed. A second integer-bitvector replay checks the whole
prefixes through 15,963 and 20,811 moves. This diagnoses the proposed frame
argument; it does not decide the modified machine's eventual halting or
exclude a different global interpretation of it.

## 10. Lossless program-data and restricted writer budget

```sh
python3 agents/theory_reduction/program_data_budget.py \
  --dag agents/machine_reduction/Dag254.v \
  --seeds 512 --output rerun/program-data/program_data_budget.json
```

The literal 219-node DAG has an exact 1,988-bit lossless prefix encoding. For
the separate 186-call AX word over 19 retained macro symbols, the best of
512 sampled RePair grammars has an exact 780-bit encoding. The script decodes
and reconstructs both inputs exactly. Its two `.bits` files are included.

The reported 250- and 124-state requirements concern only its explicitly
specified fixed-block target-address writer for these actual bit strings
(eight and seven payload bits per state respectively). They are necessary
budgets for that restricted writer, before any interpreter, not general
machine-state lower bounds or compiled machines. Other bit orders, recodings,
writers, and sharing between writer and interpreter remain outside the
experiment.

## 11. Final opcode placements and runtime controls

```sh
python3 agents/machine_reduction/opcode_permutation252.py
python3 agents/machine_reduction/check_rotation252.py \
  agents/machine_reduction/rotation-candidates/mp-drop-swap252.json \
  --table agents/machine_reduction/rotation-candidates/mp-drop-swap252.tm \
  --physical 4,5,0,8,6,2,1,7,3 --output rerun/mp-drop-swap252-check.json
python3 agents/machine_reduction/fold_changed252.py \
  --name mp-drop-swap252 --physical 4,5,0,8,6,2,1,7,3 --start 0 \
  --output rerun/mp-drop-swap252-uniform-folds.json
python3 agents/machine_reduction/role_aware_compiler252.py
python3 agents/machine_reduction/hoisted_gate252.py
python3 agents/machine_reduction/check_rotation252.py \
  agents/machine_reduction/rotation-candidates/mp-double253.json \
  --table agents/machine_reduction/rotation-candidates/mp-double253.tm \
  --physical 4,5,0,8,6,2,1,7,3 --output rerun/mp-double253-check.json
```

The opcode driver makes exactly 12 bounded constructions: all six placements
of MP, DROP, and NIP in the three non-AX command positions, once with ordinary
NIP and once with a specialized cache-equals-one NIP. With ordinary NIP all
six tables pass 8,361 guards: identity and the MP/DROP exchange use 252 graph
states, while the other four use 253. All six specialized-NIP constructions
use 254 graph states and each fails one of its 8,352 guards. These are failed
specializations, not verified 254-state alternatives or lower bounds on
other compilers.

The exact MP/DROP-exchange runtime, its decoder-entry map, and its complete
check are included. The table's SHA-256 is
`3f20c2fb02e9642259f5c3b2dad930bb1d7d68fa2b50fcdfb956c6cfd8a3e504`.
Its separate uniform-fold sweep completes 55,471 recipes and 127,059 checks
with zero survivors. **No blank startup is certified for this 252-state
runtime.** Its command operands would also need the corresponding opcode
recoding in a source proof.

The role-aware compiler protects observed uses of rows outside source
decoding and clones conflicting decoder entries. It is a cost heuristic;
the complete independent affine check determines each output's runtime
status. Running it alone emits the particular specialized-NIP control that
passes 8,351 guards and fails one B1 continuation. The emitted table, source,
and failure record are included.

The hoisted-gate experiment tries 1,012 possible full binary actions for one
lifted B2 continuation. All 1,012 fail its first tested B2 guard; the full
ledger is included. This rejects that local compilation attempt, not the
source-level shared-transfer identity.

The `mp-double253` table implements the alternative successful-MP continuation
Dag198 followed by Dag207, leaving the consequent in both top and cache with
clean scratch registers. It has 253 working states and passes all 8,366
guards, as the final command independently rechecks. Its table and decoder
are retained; no blank bootstrap is certified for it. The table construction
is the explicit local extension of the cache-MP baseline described in
`agents/machine_reduction/RESEARCH_FINDINGS.md`.

The short mathematical note
`agents/theory_reduction/nip_macro_obstruction.md` proves the separate,
restricted obstruction to emulating NIP by a fixed sequence of unchanged
MP/DROP/AX commands on every Safe state. It does not exclude changing an
operation's interface or constructing a different proof search.

## Packaged scope

The optional payload intentionally contains no compiled programs, Python byte
code, intermediate superseded zero-run frontiers, or unneeded upstream
compiler implementations. Final unsuccessful opcode and hoisted-gate
experiments are included with their explicit failure records. The main archive
separately preserves the canonical table, exact blank-frame certificate,
2,998-pair source-binding certificate, and the ordinary mathematical proof.
The optional experiment package supplies no additional local Lean build or
serialized proof object inside ZFC.
