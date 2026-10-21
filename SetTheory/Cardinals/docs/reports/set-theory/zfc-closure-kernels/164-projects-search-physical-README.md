# Additional bounded physical searches around K217

This packet records additional searches on the exact accepted K217 native table. **None produced a 216-state candidate.** A failed finite-window proof search is neither a semantic counterexample nor a lower bound on state count.

The input is the deterministic two-symbol table with initial state 0, separate halt 254, and 217 working states. Its SHA-256 is:

`b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088`

Every Python driver requires `--baseline` and verifies that hash. The driver output directory is explicit. Python scripts use the standard library; the free-row search additionally needs a C++17 compiler. Run Python without optimization, so assertions remain enabled.

## Domain and proof-search bound

All searches use radius 7, giving a 15-bit local tape window, and at most 97 transitions on either side of a proposed positive common-endpoint diagram. Shifting the window introduces either possible exterior bit. Starting with all windows at state 0 gives an inductive overapproximation of all initial tapes. It contains 962,479 working-state contexts (963,215 including halt contexts).

The separate blank-window search begins with the zero window at state 0; its exterior is still arbitrary. It includes the blank-tape execution and converges to 949,981 working-state contexts (950,717 including halt). This is a stronger initial condition than the all-tape domain; it is not a full reachable-configuration characterization.

A successful diagram must have positive old and new lengths, end in matching state/head/entire window or matching halts, and never read beyond the represented window before joining. Unchanged exterior cells then give whole-tape equality. These scripts are discovery experiments. No candidate reached independent acceptance, and no proof-assistant endpoint is supplied.

## Actual completed experiments

| Experiment | Executed census | Survivors |
|---|---:|---:|
| Single-entry state bypass, arbitrary incoming action | 108 states; 93,744 specifications | 0 |
| Shared-row merge with both incoming writes/moves free | 56 unordered pairs; 777,728 specifications | 0 |
| Same 56 pairs with both keeper rows also free | 17,633,292 local-diagram trials; all 56 pairs completed | 0 |
| Auxiliary-selector rewrites composed with a merge | 206 unordered pairs; 657,432 specifications | 0 |
| All ordered pair folds under the blank-window invariant | 46,872 ordered pairs; 647,136 specifications | 0 |

The independent row census checks every transition row and finds 510 alternative actions passing its local diagrams, in addition to the 434 original actions. These supply 813 nontrivial combinations of the two rows of an auxiliary helper state. The auxiliary-selector experiment combines these helper variants with an arbitrary new write/move into that helper for the nonshared keeper branch, then would invoke the independent joint checker on any local survivor. There were no local survivors.

The free-row C++ experiment synthesizes rows lazily when a test execution first reaches them. Its measured count is a count of local-diagram trials, **not** a count of distinct complete machine specifications. The retained log ends with `timedout 0`.

Partial first-incoming-edge probes and sample invalid tables are not included. Neither are generated executables or the redundant 5.3 MB domain export. The domain is regenerated from the pinned table.

## Reproduce

Run these commands from this directory, replacing the baseline path and temporary output path with suitable values:

```bash
baseline_path=/absolute/path/to/k217.native.tm
search_output=/absolute/path/to/new-search-output

python3 -B search_bypass.py --baseline "$baseline_path" --output "$search_output/bypass"
python3 -B search_marker_entries.py --baseline "$baseline_path" --output "$search_output/marker-entries"
python3 -B search_row_variants.py --baseline "$baseline_path" --output "$search_output/variants"
python3 -B search_helper_rewrites.py --baseline "$baseline_path" --variants "$search_output/variants/row-variants.json" --output "$search_output/helper-rewrites"
python3 -B search_blank_folds.py --baseline "$baseline_path" --output "$search_output/blank-window"

python3 -B export_search_domain.py --baseline "$baseline_path" --output "$search_output/domain"
g++ -O3 -std=c++17 search_free_rows.cpp -o "$search_output/search-free-rows"
"$search_output/search-free-rows" "$search_output/domain/search-domain.txt" "$search_output/free-rows" 240
```

The helper-rewrite driver also accepts the supplied `results/row-variants.json` by default. For an entirely fresh replay, use the explicit `--variants` command above. The helper-rewrite driver has a 240-second soft limit; compare its completed pair count with 206 to determine whether a new invocation completed. The C++ command's final argument is a wall-time limit in seconds. Other drivers run their finite stated families to completion.

The result files under `results/` are the executed research receipts from this session before command-line portability edits. Those edits change input and output path handling and add a pinned-hash check, without changing the search loops. The portable bypass driver was freshly replayed and reproduced 108 states, 93,744 specifications, and zero hits; the C++ version was rebuilt after its interface edit. Original timing fields are measurements from their recorded runs and are not expected to repeat.

## Provenance

`check_joint_fold.py` and `filter_source.py` are copied from the existing ProveIt K217 research packet at commit `d3d6b8c14e1ddff37eb1417c5448caa41cfd6da7`, under:

`Computability/BusyBeaver/Research/ZFC/candidate-k217/research/omit-zero-fold-search/folds/`

Their original source headers are retained. The remaining drivers implement the new search families and portable reproduction interface. The ProveIt MIT No Attribution license is retained in `LICENSE`. A file inventory with SHA-256 hashes is in `manifest.json`.
