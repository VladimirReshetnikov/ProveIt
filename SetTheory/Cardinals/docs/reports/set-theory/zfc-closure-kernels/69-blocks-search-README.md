# Optional searches and reproduction

All commands below are run from the archive root. Python scripts use the packaged relative paths; no external ProveIt checkout is required. C++ programs require a C++17 compiler. These are finite research searches, not proofs that no smaller consistency machine exists. They can overwrite their own generated results. The main `python3 -B code/verify_all.py` is the appropriate fast certificate check and does not rerun these large families.

## Local incoming-action domains

```sh
python3 -B search/incoming_action_search.py --oracle arithmetic --output results/recomputed-incoming.json
```

The complete recorded family contains 254,856 action trials. Supported oracles are `strict`, `source`, `exact`, `quiet`, `workspace`, `combined`, and `arithmetic`. The six compared recorded runs are strict, source, quiet, workspace, combined, and arithmetic; `exact` is an additional available wrapper. Use `--seconds 30` for an explicitly partial exploratory run. A locally acceptable replacement action is not an accepted whole-state deletion: every simultaneous choice still needs a joint replay.

Exact joint obstruction certificates are replayed separately:

```sh
python3 -B code/verify_union_obstructions.py
```

That verifier uses exact sparse configurations on an unbounded tape. It does not merely repeat the bounded searches that discovered the graphs.

## Contextual source emission

A fast baseline reconstruction and complete guarded replay is:

```sh
python3 -B search/context/recompile_decoder.py --output results/recomputed-emitter-baseline.json
```

The unchanged input must give 203 decoder DAG nodes, 246 initialized runtime states, 8,391 guarded cases, and no failures. This portable entry point was checked after packaging; the recorded result is `results/portable-emitter-baseline.json`.

The two source-invariant dead-loop deletions can be regenerated and then separately emitted:

```sh
python3 -B search/context/source_prune.py
python3 -B search/context/recompile_decoder.py search/context/pruned-dag-1.json --output results/recomputed-second-prune.json
```

The second deletion has 204 shared decoder nodes and 247 initialized runtime states. This does not verify a changed blank initialization. Other portable source drivers are `search/context/rotation_246_search.py` and `search/context/rotation42_congruence.py`. Their results and precise completion status are in `search/context/SEARCH-SUMMARY.md` and `search/context/search-ledger.json`. The latter congruence driver uses a bounded greedy search, not exhaustive minimization.

## Runtime and transfer experiments

The following entry points resolve all imports and data within this archive:

```sh
python3 -B search/runtime/pivot20_workspace_search.py
python3 -B search/runtime/pivot20_carry_workspace_search.py
python3 -B search/runtime/source_transfer_identity.py
python3 -B search/runtime/source_transfer_reassociate.py
python3 -B search/runtime/source_origin_reuse.py
```

Read `search/runtime/runtime-search-summary.md` for scope before running these longer finite families. The reassociation pass uses the included transfer-identity outputs. All five entry points passed syntax and import-only checks from an unrelated working directory after packaging. This is recorded in `search/runtime/portability-check.json`.

Only three representatives of the cooperative 20-to-143 pivot preserve every transported macro row; the other 15 representatives' fixed-macro symbolic calls are marked exploratory. Complete finite literal screens are recorded separately. No transformed source table's blank initialization was checked. `origin-reuse-49-246-00/` is an initialized runtime example, not a new blank-start bound.

## Literal C++ screens

Create a local build directory and compile the selected program:

```sh
mkdir -p build
c++ -O3 -std=c++17 search/search_pair.cpp -o build/search_pair
c++ -O3 -std=c++17 search/search_starts.cpp -o build/search_starts
c++ -O3 -std=c++17 search/context/detector_pair_search.cpp -o build/detector_pair_search
c++ -O3 -std=c++17 search/context/detector_receiver_search.cpp -o build/detector_receiver_search
```

Examples with all input paths explicit:

```sh
build/search_pair reference/context246/machine/zfc_prefix246_old.tm 48 0
build/search_starts reference/context246/machine/zfc_prefix246_old.tm 10000000 start
build/detector_pair_search reference/context246/machine/zfc_prefix246_old.tm search/context/sites.txt
build/detector_receiver_search reference/context246/machine/zfc_prefix246_old.tm search/context/sites.txt
```

- The first command is the two-row family whose only finite macro survivor is the rejected unconditional tail trap. The 21 recorded families are represented by `results/pair-*.txt`. Across families, overlapping recipes are counted with multiplicity.
- **Use the explicit `start` argument** for the existing-label blank-start screen. Its default `seed` mode additionally edits a startup row and is a different experiment. The recorded `start` screen has a ten-million-transition cap per label and head range `[-131070,131070]`. It reaches the required root class only from old state 95 within those bounds.
- Detector screens use 25,173 concrete guarded frames, a 2,500-transition limit, at most 16 dispatcher visits, and a 512-cell tape window. The receiving-pair pass prunes nominal triples before completing them. Its 15,635,760 concrete completions are not 855,938,304 fully executed candidates.

The retimed-table screens have two required arguments, machine and sites:

```sh
c++ -O3 -std=c++17 search/context/rotation_merge_search.cpp -o build/rotation_merge_search
c++ -O3 -std=c++17 search/context/rotation_entry_search.cpp -o build/rotation_entry_search
build/rotation_merge_search search/context/rotation-0-246/machine.tm search/context/rotation-0-246/sites.txt
build/rotation_entry_search search/context/rotation-0-246/machine.tm search/context/rotation-0-246/sites.txt
```

They are finite sufficient-criterion screens. They do not prove an unrestricted lower bound for the table or for machines of a given size.

## Rejected-table repairs and exact witnesses

```sh
python3 -B search/tail_exit_search.py
python3 -B code/check_rejected.py
python3 -B code/threshold_literal_witness.py
```

The first command is a 6,860-recipe finite third-row repair screen. The other two reconstruct exact failures; they are part of the default verification. The gap-detector witness starts the modification from a frame reached by the **reference** blank computation. Its 6,012,481-step prefix must not be attributed to the modified table's own blank execution.

## Evidence categories

Preserve the distinction among a full symbolic initialized simulation, a finite literal screen, a closed-graph obstruction proof, and a verified blank bootstrap. A failed sufficient checker can reject a mathematically valid implementation that lies outside its supported proof rules. A stopped or interrupted search is recorded as such. In particular, the state-4 nondeterministic exploration and the hybrid-macro symbolic follow-up were not completed exhaustive results.
