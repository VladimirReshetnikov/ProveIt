# Contextual decoder reduction search: completion and trust scope

## Completed result and trust scope

No validated machine with fewer than 246 working states has been found. The positive results below are initialized-runtime simulations of changed source programs, or independently checked finite obstruction certificates. A blank-start calibration has **not** been verified for any changed source program in this directory. The inherited context246 reference is the baseline; every changed table discussed here is an initialized-runtime artifact only.

The baseline table is `../../reference/context246/machine/zfc_prefix246_old.tm`, with start 95, halt 254 and 246 working states. Its SHA-256 is `303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`. The baseline macro interface is held fixed through the 42 transition pairs used by the existing induction proofs. The four boundary pairs `(6,0)`, `(20,0)`, `(48,0)`, `(69,1)` are not used inside those macro proofs and can be separately tested.

## Completed fixed-table searches

| Search | Completed scope | Outcome and limitation |
|---|---:|---|
| Shorten the zero-run detector | All shorter thresholds tested against the guarded source cases | Removing 74 with 58/0→0 L 84 fails 36 guarded cases at 18 decrement leaves. The source-audit teammate separately found the first failure on the actual blank run. |
| Direct decoder-state identifications |54,390 directed identifications | No accepted symbolic simulation; fixed survivor rows and fixed macro contracts. This is relative to the affine checker and its fuel bound. |
| Per-entry target-only reroutes |23,520 edits | No whole state can be deleted with independently legal target-only entry changes. |
| Per-entry arbitrary action |254,856 main trials, plus 1,968 boundary-entry trials | Six targets have nonempty individual domains on every incoming edge; all require joint analysis because their alternatives can still re-enter the state through another unchanged edge. |
| Source-zero invariant oracle |254,856 trials over 8,385 admitted guards | Exactly the same domains as the strict oracle. Six impossible guards are omitted using an inductive source invariant valid for all nine initial register values. |
| Finite quiet-source-block oracle |254,856 trials | Exactly the same domains again. Accepts additional certified quiet source endpoints, but finds no new individually valid action in this family. |
| Detector 74 removal plus one receiving row |1,759,392 nominal action pairs, 895,440 concrete completions after partial evaluation | Zero survivors on 25,173 finite guarded frames; 2,500 steps and at most 16 dispatcher visits per trial. This is a bounded finite search, not a general impossibility proof. |
| Detector 74 removal plus both receiving rows |855,938,304 nominal action triples, 15,635,760 concrete completions after partial evaluation | Zero survivors under the same finite contract test; 884 receiving-state/write/direction families, 606.1 seconds. All macro-used pairs remain fixed. |

The completed counts are recorded in `search-ledger.json` and the matching package ledger `../../results/context-search-ledger.json`. The packaged incoming-action reports are `../../results/incoming-action-results.json`, `../../results/invariant-incoming-action-results.json` and `../../results/quiet-incoming-action-results.json`; their portable driver is `../incoming_action_search.py`. The detector two-edit family is `detector_pair_search.cpp` with `detector-pair-results.log` and an empty `detector-pair-survivors.txt`.

## Exact finite obstruction to simultaneous incoming reroutes

A set of 801 individually neutral action replacements was supplied by the finite runtime screen. Individual neutrality does not imply joint correctness: one replacement can rely on another old incoming edge to return to the state that is supposedly being deleted.

For each of eight targets, a nondeterministic overapproximation permits a fresh candidate action at every visit to any changed incoming row. Thus every fixed simultaneous choice is included. Every literal connecting path returns to a finite graph, with no required instruction endpoint or halt on a connecting path. This proves failure of the desired single-instruction simulation for the displayed concrete frame, independently of any finite execution cutoff.

| Removed state | Fixed simultaneous combinations | Closed graph nodes | Graph edges |
|---:|---:|---:|---:|
|67|1|2|2|
|122|1|2|2|
|235|1|2|2|
|42|30|2|11|
|48|8|2|3|
|69|20|2|12|
|39|60|2|5|
|30|1,906,080|5|91|

The 19 nodes and 128 edges are independently reconstructed by `../../code/verify_union_obstructions.py`, using a sparse unbounded tape representation and exact Python configurations. The complete graph nodes, transition choices, connecting literal paths, required endpoint and initial register fixture are in `../../results/union-graph-certificates.json`. `../../results/union-obstructions.json` gives the compact ledger and `../../data/neutral_rows.txt` gives the exact candidate domains.

This is an obstruction to this specified compiler-simulation family. It is **not** a lower bound for all Turing machines, and does not prove that no unrelated blank-start machine in one of these state counts can have the requested consistency behavior.

The larger nondeterministic searches for states 2, 4, 57 reached their exploration bounds and have no analogous closed-graph certificate. A separate bounded joint enumeration eliminated 2 and 57 in their fixed finite domains. Do not report state 4 as completely searched.

## Changed source programs and decoder retiming

`recompile_decoder.py` adapts the inherited contextual emitter to the exact 246 table. It freshly enumerates all leaves and derives successor paths directly, and its baseline replay passes all 8,391 guarded cases at 246 initialized runtime states. A generic break/continue option gives newly emitted control edges explicit behavior; retained old contextual rows still require a full replay and cannot be assumed correct in changed source contexts.

Two source loops are entered with a counter known to be zero:

- At prefix `11101001011000110`, the closed loop is `N(CD X, N(CI H, CC2))`.
- At prefix `11111100`, the closed loop is `N(CD T, N(CI X, CC2))`.

Replacing one such loop by a skip and eliminating closed sequential skips loses structural sharing. The baseline has 203 structural decoder nodes; removing the first, second or both gives 206, 204, 207. The freshly verified initialized-runtime table counts are 252, 247, 253 respectively. All new guarded cases pass, but these counts are **not** blank-start records. See `source_prune.py`, `source-prune-results.json`, `pruned-dag-{0,1,both}.json` and `recompile-pruned0.json`, `recompile-pruned1.json` and `recompile-pruned-both.json`.

The prior 204-node layout with maximum zero run 6 still fails 502 guarded cases, starting with its known CC 2 failure at case 139. Using generic controls only on new nodes does not repair inherited contextual decoder/primitive entries. The two original working failure ledgers are summarized here; they are not bundled as additional machine candidates.

`rotation_246_search.py` completes all 238 single closed reassociations or commuting-increment transformations generated by the inherited source grammar. There are 59 shape-bound rejections, 153 successful full guarded replays and 26 failures under both emitter modes. No initialized runtime has fewer than 246 states. Five tie 246: indices 0, 233, 235, 236, 237. Each directory `rotation-INDEX-246/` contains the changed source DAG, emitted machine and exact replay result. None has a verified blank bootstrap.

For each of these five retimings, a fresh finite regression passes 25,173 guarded frames. Then 54,390 directed decoder-state identifications per table, 271,950 total, have no survivors. The source-aware finite screen is `rotation_merge_search.cpp`; each directory contains its `sites.txt`, `merge-results.log` and empty `merge-survivors.txt`.

## Completion status of the final experiments

The stronger `detector_receiver_search.cpp` family is **complete**: 855,938,304 nominal action triples over 884 families, with 15,890 partially surviving first-row assignments and 15,635,760 concrete completions. It rewrites 58/0 and both rows of the selected non-macro receiving state. Every candidate fails the bounded 25,173-frame test. The final log line records `COMPLETE`, and the survivor file is empty. This remains a finite contract test, with the same limits as the two-edit family.

`rotation_entry_search.cpp` is also **complete** for all five 246 retimings. It checks arbitrary write/direction/existing-working-target edits on the sole external incoming edge of a removable non-macro state. There are 130,340 trials per table, 651,700 total, with zero finite survivors. Each rotation directory contains `entry-results.log` and an empty `entry-survivors.txt`. No universal replay or blank-start validation is inferred for a nonexistent survivor.

The exploratory hybrid-macro merge follow-up and the naive state 30 joint product enumeration were interrupted. Their intermediate files must not be cited as completed searches. State 30 is instead covered by the exact finite closed-graph certificate above.

## Final bounded congruence quotient

A final check on single rotation 42 starts from a 202-node source DAG and its 254-state initialized runtime. It captures 503 universally inspected transition pairs, including all 42 macro-used pairs. A congruence closure merges two states only when their observed writes and directions agree and their target states can be merged consistently. Macro representatives remain fixed; dispatcher 96 and halt 254 remain separate from every other state.

Two greedy orders were completed: source-origin candidates first, and reverse source-origin candidates first. Both produce 249 initialized states and pass a fresh replay of every changed source guarded case. The two runs test 32,136 and 32,135 seed pairs respectively. This does not prove 249 is the best quotient under all possible merge orders, and supplies no blank-start calibration.

The driver is `rotation42_congruence.py`, with summary `rotation42-congruence-results.json` and explicit quotient data in `rotation42-quotient-249/`. This was the last new search family.

## Portable package layout and replay

Paths in this summary are relative to `search/context/`. The frozen baseline material is in `../../reference/context246/`; shared verification code is in `../../code/`; the complete graph certificates and central search ledger are in `../../results/`; and the neutral action domains are in `../../data/neutral_rows.txt`. The local `search_common.py` supplies the package's common module. The inherited decoder and grammar inputs remain beside these drivers, with attribution in `SOURCE-NOTICE.md`.

The new congruence driver resolves the package root from its own location with `ROOT = Path(__file__).resolve().parents[2]`, loads shared code from `ROOT / 'code'`, and imports the inherited emitter and grammar modules from this directory. Its source-DAG root is separately named `SOURCE_ROOT` to avoid confusing that integer with the package path.

The following commands are for a future replay from the package root. Search drivers can regenerate their local result files; these commands are documentation and do not indicate that additional searches were run during packaging.

```sh
python code/verify_union_obstructions.py
python search/context/recompile_decoder.py --output search/context/recompile-baseline.json
python search/context/source_prune.py
python search/context/rotation_246_search.py
python search/context/rotation42_congruence.py

g++ -O3 -std=c++17 search/context/detector_pair_search.cpp -o search/context/detector_pair_search
search/context/detector_pair_search reference/context246/machine/zfc_prefix246_old.tm search/context/sites.txt

g++ -O3 -std=c++17 search/context/rotation_merge_search.cpp -o search/context/rotation_merge_search
search/context/rotation_merge_search search/context/rotation-0-246/machine.tm search/context/rotation-0-246/sites.txt
```

The graph verifier also accepts explicit `--machine`, `--neutral-rows`, `--obstructions` and `--output` paths. The source-invariant and quiet-block incoming checks use their separately packaged affine checkers and source certificates under `../../code/` and `../../results/`. None of these replay commands supplies a blank-start calibration for a changed source table.
