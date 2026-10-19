# Interpreter compression experiments for Routing245

This directory contains a new universally proved **local left increment**, an explicit counterexample to its unchanged-caller integration, a source-level resource-allocation obstruction, and four reproducible bounded compression searches. It does **not** contain a verified consistency machine with fewer than 245 states.

The original reference table has 245 working states. The experimental `left_increment_local244_old.tm` has 244 working states but fails the original whole-instruction contract. It is included to make that rejected experiment exact and reusable. State labels in this directory are the old labels: start 95, dispatcher 96, halt 254. The canonical 245-state table elsewhere in the package instead uses start 0, dispatcher 88, halt 245.

## Results

The three edits to rows `75/0`, `83/0`, and `131/0`, followed by deletion of state 255, yield a prefix-shifting register increment. With two zero cells before the register header, the macro increments the chosen unary register, shifts the header and preceding blocks left by one cell, and preserves the suffix. Its exact cost is `2 * width(prefix) + 6`, independent of the selected value and suffix length. The proof quantifies over all natural values and finite block lists; it uses unary and list induction, rather than finite samples.

The existing dispatcher does not provide the two-zero entry premise: its increment phase fills the gap with ones. A valid instruction fixture consequently returns with pointer `0110` instead of `01011`, even though the chosen register increments correctly. Sparse and dense transition interpreters independently agree on the full tape at this endpoint. This refutes the proposed original-source modular contract; the fixture is not asserted blank-tape reachable.

Even if that entry problem were repaired, a backend using only left increment, compensating positive decrement, and the original root-overflow allocations would satisfy `gap + sum(primary) = 187 + root_overflows` from the current seed. Two independent exact source interpreters agree that this policy implies gap 63 after 2738 instructions and gap −1 after 3235. The source trace is exact; these gaps are counterfactual resource values for the proposed policy. A changed grammar/control trace or explicit extension operation can change the obstruction's hypotheses.

All four bounded searches have zero survivors on their stated families. Their counts are recorded below and scoped precisely in `interpreter_results.tex` and `search/results.json`.

| Search | Individual trials | Past quick probes | Survivors |
| --- | ---: | ---: | ---: |
| Selected-row pair merge, exact tape | 119,560 | 54 | 0 |
| Selected-row pair merge, relaxed frame | 119,560 | 54 | 0 |
| Single-entry state splice | 133,712 | 163 | 0 |
| Adaptive multi-entry edge edits | 175,680 | 712 | 0 |

The multi-entry trial count counts individually screened edges, not joint candidate tables. At most 100,000 combinations per covered state are checked. All runs use fuel 20,000 and tape range −64 through 1983. Exceeding a bound rejects a candidate from the screen, without proving that it can never reach the target. These results do not establish unrestricted state minimality.

## Reproduce the core results

Python 3.10 or later and its standard library suffice. Run from this directory, without Python's `-O` option:

```bash
python3 prove_left_increment.py
python3 check_integration_counterexample.py
python3 check_gap_budget.py
```

The scripts overwrite their corresponding JSON evidence files beside the scripts. All paths are relative to the scripts, so these commands also work after copying the entire directory. The output statuses deliberately separate the proof scopes:

- `PASS_LOCAL_BOX_CONTRACTS_ONLY`: universal local block/list calculation; the full edited machine remains rejected.
- `PASS_EXACT_INTEGRATION_COUNTEREXAMPLE`: independent dense and sparse replay of the failed whole-instruction fixture.
- `PASS_TWO_EXACT_SOURCE_REPLAYS`: agreement on 3235 exact source steps and the resource recurrence witnesses.

The LaTeX section `interpreter_results.tex` is intended for `\input{interpreter/interpreter_results}` in the parent report. It needs standard LaTeX, `amsmath`, and `amssymb` and supplies the mathematical induction proofs, boundary conditions, and scope of the computational evidence.

## Replay the optional compression searches

A C++17 compiler (`g++` or `clang++`) is also required. The wrapper verifies and decompresses the compact fixture, compiles the selected sources, and writes logs and summaries under the requested output directory:

```bash
python3 replay_searches.py --output /tmp/routing245-interpreter-searches
```

To select a subset:

```bash
python3 replay_searches.py --output /tmp/routing245-pair-search --which exact_pair semantic_pair
```

Other names are `single_entry_splice` and `multi_entry_splice`. Timing and quick-probe counts can depend on compiler/library implementation; the search definitions and fixture are fixed. The baseline is checked against every fixture before a search starts. The 8385 fixtures exercise all 490 transition rows, and the maximum baseline execution takes 2686 moves. The compressed fixture is about 436 KiB; it expands to about 24.4 MiB only in a temporary directory.

## Inventory

| File or directory | Purpose |
| --- | --- |
| `interpreter_results.tex` | Mathematical report section and all claim boundaries |
| `prove_left_increment.py` | Universal unary/list macro derivations |
| `left_increment_local_proofs.json` | Local symbolic derivation output |
| `left_increment_local244_old.tm` | Exact 244-state experimental table, rejected for unchanged-caller integration |
| `check_integration_counterexample.py` | Independent sparse/dense TM replay |
| `integration_counterexample.json` | Full counterexample tape and compact comparison |
| `check_gap_budget.py` | Two independent exact source interpreters and resource recurrence |
| `gap_budget_counterexamples.json` | Milestones, transition counters, trace hashes, and recent source steps |
| `replay_searches.py` | Portable optional search driver |
| `search/*.cpp` | Four fixed bounded search programs |
| `search/results.json` | Recorded bounds, counts, timing, fixture/table hashes, and scope |
| `search/edge-alternatives.txt` | Individually surviving edge alternatives from the adaptive screen |
| `search/cases.txt.gz` | Compact input fixture, including the exact reference table |
| `reference/` | Minimal original table, source sites, inherited macro checker dependencies, notices and licenses |

The `reference/` subset duplicates a small part of the parent package's `reference/zfc245` intentionally so that this experiment directory remains independently replayable. The inherited macro checker rebuilds its older context246 table on import; the new proof script explicitly replaces its active table with the supplied experimental table before deriving any new result.

## Fixed provenance and digests

The source is ProveIt at commit `6446ff5668307a2ac6aee1896037f0b792090389`, with the baseline recovered from its incoming Routing245 proof package dated 2026-10-18. The parent report identifies the incoming archive and its full provenance. Original notices and licenses are preserved under `reference/`.

| Artifact | SHA-256 |
| --- | --- |
| Reference old-label table | `f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267` |
| Experimental 244-state table | `0ed2e09d128b2942528eeae58bc6a12a950312fbca72cd43c90b7526b964ee42` |
| Exact 6460-leaf source sites | `f77a3fb9729382a0b8cd24d480639862b63ecb76bbc205542d1fc7077c025745` |
| Compressed search fixture | `3ebf4ea86da4a6bcd12b857cb67b3ba6b32e597b94eb8bfeef5e3ff03cddf31d` |
| Decompressed search fixture | `71fd6d7d0460c3f920ba945c04f2e3a1b571ce070e445ae019417ff0d675abc1` |

The new scripts and prose were prepared for this investigation on 2026-10-18. The search implementations adapt the incoming `beyond246` search framework; the local symbolic proof reuses its inherited audited unary/list rules. These adaptations are not claims of authorship of the reference machine or inherited verifier.
