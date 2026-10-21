# Portable K219 machine-search supplement

**Status: no machine with at most 218 working states has been validated here.**
This directory preserves finite negative searches, independently checked
macro contracts, and reproducible search tools. It is not a state-count lower
bound. `search_snapshot.json` distinguishes completed families from partial
ones at the snapshot time.

The baseline table is the repository's K219 construction, with 219 working
states, halt label 254, and native start label 0. The exact table and ordered
source are in `inputs/`. Their SHA-256 values are:

- Table: `b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26`
- Source: `0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789`

The five inherited modules/data files in `vendor/K221_minimal/` are unchanged
copies from the K221 construction package. `vendor_provenance.json` records
their original paths and hashes. The supplied drivers use Python's standard
library; the solvers use a C11 compiler and the C standard library. No network
access, package installation, or repository checkout is needed for the commands
documented below. The historical direct-entry local-window search in
`src/search_rotations.py` is archival and has an additional repository
dependency described below; the portable drivers do not use that entry point.

## Rebuild the observations

Run commands from this directory. Assertions must remain enabled; do not use
Python's `-O` switch or set `PYTHONOPTIMIZE`.

```sh
python3 src/source_facts_portable.py \
  --baseline vendor/K221_minimal \
  --sites inputs/sites219.json \
  --output regenerated/facts.json

python3 src/generate_frames_portable.py \
  --baseline vendor/K221_minimal \
  --table inputs/k219.native.tm \
  --sites inputs/sites219.json \
  --facts regenerated/facts.json \
  --output regenerated/ordinary

python3 src/generate_macro_frames_portable.py \
  --baseline vendor/K221_minimal \
  --table inputs/k219.native.tm \
  --sites inputs/sites219.json \
  --ordinary regenerated/ordinary \
  --mode combined \
  --output regenerated/combined
```

The source invariant separates the exact values 0..7 from values at least 8.
The ordinary screen selects one Cartesian-minimum input per admitted guard;
those inputs need not be reached by the actual blank run. Its 6,162 reference
outputs agree with an independent primitive specification. The combined
screen has 6,646 cases: 6,076 ordinary observations, 375 whole capture gates,
18 NIP comparisons with scratch6=1, 162 whole MP comparisons, and 15 whole
proof-index refills. Its reference outputs are checked against independent
register-level contracts, including spare counts and gap changes.

The combined generator reproduces the archived binary fixture, witnesses,
macro-prefix file, and interval file byte for byte. The binary fixture's hash
is `e50f919d12a525f7f63c84678c9fb5c26b2de8dd2c136f2d5b054948e50872cf`.
The other generator modes are `equality`, `refill`, and `gate`.

## Run a finite search

```sh
cc -O3 -std=c11 -Wno-unused-result src/whole_primitive_folds.c -o solver

GENERAL_FRAMES=1 FRAME_ANCHOR=75 ADAPTIVE_ANCHOR=1 CYCLE_PRUNE=1 \
  OPEN_MACROS=fixtures/combined/macros.txt \
  INTERVAL_MACROS=fixtures/combined/intervals.txt \
  ./solver inputs/k219.native.tm \
  fixtures/combined/frames.bin fixtures/combined/witnesses.txt hits.txt \
  both_pre pairs/refill_priority_pairs.txt
```

`both_pre` synthesizes both rows of the retained state after redirecting all
incoming edges of the removed state. Partial execution stops as UNKNOWN at
the unassigned row; UNKNOWN is not success. Every complete hit must pass all
finite observations. The baseline table must first pass every fixture.

Use `sole` in place of `both_pre pairs/...` for sole-incoming-state deletion.
Omit both final arguments for the family in which a previously common row
is retained and the other row is synthesized. `VERIFY_ONLY=1` runs only the
positive control.

`GENERAL_FRAMES=1` preserves the exact padded source counter and all nine
primary values at the observation boundary, while allowing translation,
any header gap of at least 64, arbitrary spare-block values, and at least
the original number of spare blocks. The tape window is 512 cells, with
origin offset 128. The finite runtime allowance is 4 times the reference
duration plus 1600 steps, measured from the cached first modified state.
Set `COUNT_PREFIX_STEPS=1` to charge the cached prefix to that allowance too.
The archived completed searches use the former convention. Both are finite
screens; neither is an unbounded semantic proof.

`CYCLE_PRUNE=1` rejects an exact repeated state/head pair when no intervening
write changed any tape cell. `DROP_TAG_MODE=1` complements the incoming write
bits of the deleted state. `DROP_MOVE_FLIP=1` reverses the incoming moves of
that state; the cached entry head is displaced by minus twice the original
incoming move. The movement pair lists contain only states with a uniform
incoming direction, in both permitted orientations. These options describe
specific additional families, not all compiler transformations.

The auxiliary fixture and pair-list generators also accept explicit paths:

```sh
python3 src/relax_gate_d_frames.py \
  --input fixtures/combined --output regenerated/gate_dead_d_cpositive \
  --contract c_positive
python3 src/move_flip_pairs219.py \
  --table inputs/k219.native.tm --pairs-dir pairs \
  --output-dir regenerated/movement_pairs
```

The former permits arbitrary output D4 at whole capture-gate boundaries only
when the gate's input c is positive, and at unequal MP exits. All other primary
registers remain exact. These are finite discovery contracts; a concrete hit
would need an unbounded macro proof and the reset/completeness argument. The
corresponding solver command must set `LIVE_REGISTERS=1` to use the masks.
The narrower earlier contract is available as `--contract a_lt_c`.

## Several mutable actions

```sh
cc -O3 -std=c11 -Wno-unused-result src/multirow_folds.c -o multi_solver

GENERAL_FRAMES=1 MULTI_ROWS='103 1 113 0 198 0' REMOVE_STATE=302 \
  OPEN_MACROS=fixtures/equality/macros.txt \
  ./multi_solver inputs/k219.native.tm \
  fixtures/equality/frames.bin fixtures/equality/witnesses.txt hits.txt
```

`MULTI_ROWS` is a sequence of state/read-bit pairs. `REMOVE_STATE` is forbidden
as a target in the synthesized table. An optional `REDIRECT_STATE` first
redirects its incoming edges to a retained state; incoming bit tagging is
also supported. `MAX_NODES` limits the search, and the report explicitly says
`BUDGET_REACHED` if the limit interrupts it. `PIN_BASE_ACTIONS=1` supplies a
positive control by fixing the mutable rows to their original actions.

The optional source-reassociation driver is also supplied. It needs its
executable at `src/whole_primitive_folds` and explicit inherited paths:

```sh
cc -O3 -std=c11 -Wno-unused-result src/whole_primitive_folds.c \
  -o src/whole_primitive_folds
BASELINE221=vendor/K221_minimal \
  SEARCH_TABLE=inputs/k219.native.tm SEARCH_SITES=inputs/sites219.json \
  ROT_FRAME_META=fixtures/ordinary/frame_metadata.json \
  ROT_WITNESSES=fixtures/ordinary/witnesses.txt \
  WHOLE_ROT_OUT=regenerated/rotations python3 src/whole_rotations.py 2
```

This driver checks the unchanged ordinal control graph and then runs finite
primitive controls before its mutation screens. Passing those controls is
not an unbounded proof of a reassigned arithmetic helper.

`ROT_SOLVER` can select a compiled solver at another path. Bundled input and
vendor paths are detected automatically; the explicit command above makes
every input clear. Setting `VERIFY_ONLY=1` and using depth `0` runs the baseline
positive controls without a mutation search.

**Archival entry point:** `src/search_rotations.py` supplies the grammar helper
functions imported by `whole_rotations.py`. Its historical direct command
`python3 src/search_rotations.py ...` additionally calls `inv_fold.py` and
`sim_fold.py` from `Computability/BusyBeaver/Research/ZFC/candidate-k221/code`
in the ProveIt checkout. Those modules are not included. To reproduce that
older local-window experiment, set `LEGACY_FOLD_CODE` to that directory and
provide `BASELINE221`, `SEARCH_TABLE`, and `SEARCH_SITES` explicitly as above.
The direct entry point gives a clear dependency error when those modules are
absent. It is not included in the standalone reproduction claim.

## Unbounded primitive replay

```sh
python3 src/verify_runtime_portable.py \
  --baseline vendor/K221_minimal \
  --table inputs/k219.native.tm \
  --sites inputs/sites219.json \
  --output regenerated/universal_runtime.json
```

This driver uses induction over unary runs and spare lists to check the
primitive runtime for arbitrary natural primary values, gap, and spare
values/list length. It reports `NOT_PROVED` on a failed proof attempt;
that status alone is not a counterexample. Blank initialization and the
source program's logical calibration are separate obligations. A mutant
that preserves only a larger atomic contract will need a corresponding
all-natural macro proof, not this unchanged primitive replay alone.

## Reading the results

`machine_search_section.tex` states the macro contracts and the completed
families. `FINAL_SEARCH_SUMMARY.md` also records the earlier 220-state work.
`search_snapshot.json` and the preserved logs give exact completed or partial
status. A `PROGRESS` line is not exhaustion. Search counters from different
observation contracts must not be added as one exhaustive search.

There are no finite positive hits claimed as a solution in this supplement.
In particular, the transfer-swap source experiment is marked rejected:
its fresh 219-state table selects CI1 where the changed source requires CI5.
