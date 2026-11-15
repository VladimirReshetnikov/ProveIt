# Search evidence and reproducible experiments

These files record attempts to reduce the state count and the discovery of the
two transition shortcuts used elsewhere in this package. **No accepted machine
with fewer than 194 working states was found.** The positive construction and
its verification are in the package's `machines/`, `verification/`, and report;
the experimental raw tables here are not additional accepted machines.

The source snapshot is ProveIt commit
`883da8d55452ea097910ed2509a1eefc833ce292`. Search code, frozen inputs, completed
output logs, and explicit partial-run receipts are included. Compiled binaries,
Python caches, and large transient search pools are omitted.

## Recorded results

| Experiment | Actual scope completed | Result and interpretation |
| --- | --- | --- |
| Nine-register allocation | All 362,880 permutations; an earlier slot-6-fixed run covered 40,320 | The maximum matching of individually eligible predecessor-bit folds is 7 for every allocation. This excludes eight disjoint folds of the exact tested 1/3-step template from this raw 201-state parent. |
| Closed four-operand association | All five binary associations | Two raw tables have score 194 and three have score 195. Each expands to the same primitive instruction array. These are experimental raw tables; score is raw states minus a matching upper bound. |
| Expanded operand reader, original fixed part | At least 1,604,000 flushed proposals; last logged time 138.146 s | Resource-killed, exit 137, before the requested 300 s. Best recorded penalized effective score 60; no strict hit in the recorded prefix. |
| Expanded operand reader, B selector | 2,216,629 proposals, 375,878 accepted moves, 240.005 s | Completed the requested 240 s. Best penalized effective score 60 and zero strict hits. |
| Push/Copy exposure | At least 960,000 flushed proposals; last logged time 135.16 s | Resource-killed, exit 137, before the requested 180 s. Best recorded penalized effective score 60; no strict hit in the recorded prefix. |
| Exact-tape shortcut discovery | History depth 3, trace cap 13, unlimited branch budget | Completed; two candidates. The portable CLI was replayed and reproduced the saved candidate records exactly. |
| Deeper shortcut discovery | History depth 6, trace cap 19, 20,000 recursive visits per context | Completed; the same two row replacements, with four history contexts for row `(26,1)` instead of one. |

The effective grammar objective has a fixed contribution of 134 controls.
A score of 59 with no extra penalties would therefore be a nominal 193-state
candidate, still needing exact source, physical runtime, and blank-start
acceptance checks. A score of 60 is the original 194-state target. No accepted
strict improvement is hidden in these search artifacts.

The allocation matching bound concerns a narrowly specified family of rewrites.
Every edge must satisfy its individual provider contract, but a matching alone
does not prove that all its rewrites remain compatible after composition. Its
size is an upper bound, which suffices to exclude an eighth disjoint eligible
fold in this family. It is not a lower bound on the state complexity of the
consistency problem. Likewise, a failed randomized search proves no general
impossibility result.

## Reproduction environment

Run the following commands from the root of the extracted package. Python 3
with its standard library and `g++` with C++17 support are sufficient for these
experiments. Run Python normally, without `-O`, so that identity assertions
remain enabled. `-B` prevents cache files. Use a fresh scratch output directory:

```sh
mkdir -p /tmp/pa194-research-replay
```

The two randomized search implementations retain a growing pool of DAG nodes.
They can consume substantial memory, as the two recorded exit-137 terminations
demonstrate. Their stopping rule uses elapsed time; the same seed preserves the
proposal stream until stopping, but does not guarantee the same number of
proposals on a different machine or under a different concurrent workload.
The recipes below reproduce the configured experiments, not a guarantee of the
original elapsed-time totals or resource failures.

### Exact register-allocation screen

```sh
g++ -O3 -std=c++17 research/permutation_research/permutation_folds.cpp \
  -o /tmp/pa194-research-replay/permutation_folds
/tmp/pa194-research-replay/permutation_folds \
  research/permutation_research/unfolded201.native.tm \
  > /tmp/pa194-research-replay/permutation_hits.jsonl \
  2> /tmp/pa194-research-replay/permutation_log.txt
```

Append `fixed6` as the second program argument to reproduce only the earlier
40,320-case screen. The authoritative bundled full log and receipt are
`permutation_research/permutation_all_log.txt` and
`permutation_research/permutation_receipt.json`. The frozen raw-table SHA-256 is
`b25933d14de19f72709bdecf7a67a4e21c150f525cf61ec76c074ac577d6cc87`.

### Five closed operand trees

```sh
python3 -B research/operand_trees/reproduce.py \
  --output /tmp/pa194-research-replay/operand_trees
```

This deterministic enumeration loads the packaged ORH source and raw table,
uses the vendored compiler in `expanded_operand_reader/vendor/`, and asserts
identity of the complete primitive instruction array for every association.
It writes five raw tables, their fold opportunities, and `summary.json`. This
portable invocation was replayed; all five summaries and raw table bytes agree
with the recorded artifacts. The matching scores do not replace subsequent
composition and runtime validation.

### Expanded operand-reader grammar

This experiment exposes the single `node75` occurrence into
`((node32,(node53,node55)),node65)`, keeping the existing fixed reader 213 and
its other uses. It adds the two atom controls 104 and 107 to the dictionary and
recognizes the existing subtree controls 185, 92, and 213. The emitter word
grows from 190 to 193 macro tokens without changing the initial expanded
primitive instruction array.

Regenerate deterministic inputs in a copied directory to preserve the original
receipts:

```sh
cp -R research/expanded_operand_reader /tmp/pa194-research-replay/operand
python3 -B /tmp/pa194-research-replay/operand/setup.py
g++ -O3 -std=c++17 /tmp/pa194-research-replay/operand/search.cpp \
  -o /tmp/pa194-research-replay/operand_search
/tmp/pa194-research-replay/operand_search \
  /tmp/pa194-research-replay/operand/templates.txt \
  /tmp/pa194-research-replay/operand/leaf_attrs.txt \
  /tmp/pa194-research-replay/operand147 300 147
/tmp/pa194-research-replay/operand_search \
  /tmp/pa194-research-replay/operand/templates_B.txt \
  /tmp/pa194-research-replay/operand/leaf_attrs.txt \
  /tmp/pa194-research-replay/operandB148 240 148
```

`expanded_operand_reader/search_receipt.json` distinguishes the partial and
completed runs and hashes their inputs and logs. `make_receipt.py` regenerates
that receipt from the preserved logs, with the recorded exit-137 status of the
first run. It does not rerun either search. The deterministic setup has been
replayed separately. Search moves rewrite all occurrences of a selected DAG
subtree; the previous parameter-renaming moves are disabled because expansion
changes source-word offsets.

### Push/Copy exposure

The frozen input expands `node55` into `(node49,node54)`, `node58` into
`(node49,node57)`, and `node70` into `(node49,node69)`. This permits association
and sharing across boundaries previously hidden inside those macros. The
provided `meta.json` describes the expanded input. Reproduce the configured
search directly from the frozen input:

```sh
g++ -O3 -std=c++17 research/push_copy_exposure/search_exact.cpp \
  -o /tmp/pa194-research-replay/push_copy_search
/tmp/pa194-research-replay/push_copy_search \
  research/push_copy_exposure/input.txt \
  research/push_copy_exposure/attrs.txt \
  /tmp/pa194-research-replay/push_copy 180 7319415
```

`push_copy_exposure/receipt.json` records only the completed, flushed prefix
of the interrupted run. It must not be described as a completed 180-second
search. No candidate from it was accepted as a new consistency machine.

### Exact-tape shortcut discovery

The portable script defaults to `reference/PA194ORH/machine.native.tm`, with
initial control 74 excluded from history-based discovery. It follows all
incoming paths of the selected length, then universally branches on previously
unread tape bits while searching for a one-step action with the same resulting
full tape, control, and head position. The configured trace and branch limits
bound discovery; reaching a limit is not evidence of impossibility.

```sh
python3 -B research/shortcut_search.py \
  --history-depth 3 --trace-cap 13 --branch-budget 0 \
  --output /tmp/pa194-research-replay/shortcuts3.json \
  --receipt /tmp/pa194-research-replay/shortcuts3_receipt.json
python3 -B research/shortcut_search.py \
  --history-depth 6 --trace-cap 19 --branch-budget 20000 \
  --output /tmp/pa194-research-replay/shortcuts6.json \
  --receipt /tmp/pa194-research-replay/shortcuts6_receipt.json
```

Use `--table PATH` and `--start-state N` for another complete native table.
The saved original logs are `shortcuts.log` and `shortcuts6.log`; the depth-3
candidate list is `shortcuts.json`. The row replacements are `(26,1): 1R42 ->
1R91` and `(101,0): 0L26 -> 0R17`. These are discovery outputs. Acceptance still
requires an argument covering reachable histories, initial prefixes shorter
than the chosen history depth, and composition with other edits. The separate
verification and transfer proof in this package supply the positive argument
for the delivered designs.

## Existing 193-state candidate census

The portable census screen lives in `../comparison/screen193.py`, with full
results in `../comparison/screen193.json` and summary in
`../comparison/screen193_summary.json`. It tries every working control as the
blank start of each of the 55 recognized 193-state graphs. Read the
qualifications there: a finite cap remains unresolved, and easily provable
nonhalting is not a PA-consistency calibration. The old duplicate script in
this directory was removed to avoid retaining a nonportable second version.

## Proof and provenance limits

These experiments do not complete the repository's pending base equivalence
between its PA consistency program and `Con(PA)` in intuitionistic PRA. The
new-machine transfer theorem, and its dependence on that base calibration,
are stated in the report. Neither finite execution nor an unchanged source
instruction array alone proves that base theorem.

The search and compiler sources adapt the supplied ProveIt research packets;
preserve the upstream notices provided in the enclosing package. No new
technique is claimed for inherited grammar moves, the existing B selector,
or matching-based context-fold screens. The recorded facts are the exact
tested families, their outcomes, the new compositions, and the separately
verified transfer results.
