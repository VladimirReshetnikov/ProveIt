# A finite incoming-edge elimination search

The recorded search found **no accepted state deletion** in the specified
template on the 94 distinct 194-state table classes of the current census.
This is computational negative evidence for a restricted optimization rule.
It is not a lower bound on Turing machines, and the census includes diagnostic
tables as well as proposed consistency machines.

## What was searched

For each input table, the algorithm computes a finite overapproximation of
the tape windows reachable from its selected blank start. A window has
`2 * radius + 1` cells. Whenever a step exposes a new boundary cell, either
value is allowed. Consequently this abstraction includes every actual blank
run window; it can include many impossible windows.

For every working state other than the selected start, the search tries to
remove that state. It can change **each incoming transition separately**,
including its written symbol, direction, and successor. This permits more
than identifying two whole controls. The replacement first action can have
either write bit, either direction, and any remaining working successor.

For each reachable abstract input window of that incoming row, the new
fragment must match a positive-length prefix of the old computation exactly:
same control, head displacement, and entire window. The old prefix has at
most 12 steps. The replacement computation is bounded as recorded in the
catalogue. Both computations stay inside the window until their endpoint.
The replacement fragment cannot execute the removed state or any row being
changed. Thus independently selected replacements cannot invalidate each
other's detours. No search result was promoted on the basis of a successful
bounded blank run.

The 89 placed classes were searched with radius 6 and a 128-step replacement
bound. The five incoming additions were searched with radius 8 and a
256-step bound. All runs completed with zero candidate deletions.

These limits are part of the result. The rule excludes longer detours,
different tape encodings, simultaneous removal of several controls,
additional helper states, and rewriting the start configuration. Moreover,
overapproximation can reject a transformation that is valid only under a
stronger source invariant.

## Reproduction

The portable replay needs Python 3 and a C++17 compiler:

```sh
python3 replay.py --output replay.json
```

Use `--index 0` to replay just one input. Every table's bytes are checked
against the SHA-256 in `catalogue.json`. The replay also checks that all 193
eligible deletion targets were considered. `summary.json` records the
original outcomes, including the additional, deeper primary/new-loop
experiments and the separate scanner-composition experiment.

Use `python3 replay.py --deep` to replay the three deeper searches in
`deep_catalogue.json`. Their completed replay is retained separately in
`replayed_deep_results.json`.

The terminal label is not a working state. A table's selected start is
recorded independently: explicit starts and dense-table start zero are used
where available; the native-numbering tables in this corpus use control 74.
The selected-root convention is a search input, not a proof that a diagnostic
table has a calibrated startup.

## Additional experiments

The primary table and the new loop candidates 6 and 7 also received a deeper
search with radius 9, an old-prefix bound of 48, and a replacement bound of
512. These yielded no candidate.

For each of new loop candidates 3, 6, 7, 8, 9, 11 and 12, we composed the
previously supplied root/MP source rotations with a standalone reader for
the changed node20 history and a shortened return scanner. The complete
resolved graph still had the same 3,673 primitive instructions, and the
local fold checks passed. Each resulting 194-state table failed exactly 47
of the 4,780 symbolic source outcomes. These constructions are rejected.
The full failed-outcome lists are in `scanner_composition_results.json`.
The input source DAGs, raw tables, rejected tables, and a portable replay are
in `scanner_composition/`. From this directory, use:

```sh
python3 scanner_composition/replay.py
```

Add `--index 6` for only the LC composition. This replay uses the inherited
symbolic arithmetic-block contracts to check the source outcomes; it is a
failure screen, not an independent formal verification of those blocks.
Its two small vendor modules come from the supplied PA1944L construction
and are covered by the source attributions and license notices of the
enclosing package.

`reverse_helper/` records a separate, interrupted attempt to repair the
shortened scanner by changing the AX grammar and sharing a reversed reader.
Its process did not complete the requested time budget. The exact retained
checkpoint and its limitations are stated in that directory; it is not part
of the completed 94-table search.

## Provenance

The source snapshot is ProveIt commit
`32d0d8b7d93a63ad4106c18cdb29b37927acdad2`.
`catalogue.json` identifies every original path and exact input bytes.
The five incoming additions were extracted from the archives at that
snapshot, as identified by the encompassing report's inventory.

The window abstraction and finite detour method build on the supplied
`pa194_conpa_2026-11-13/search/action_merge.cpp`. The incoming-edge deletion
implementation and multi-prefix comparison in `edge_delete.cpp` were written
for this investigation. The accompanying report credits the inherited
machine, compiler, and arithmetic runtime sources and preserves their
license notices.
