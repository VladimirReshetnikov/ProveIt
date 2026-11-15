# Source-level and shared-forest reduction searches

These are reproducible bounded negative searches accompanying the separately constructed 194-state machine. **No sub-194 machine and no 194-state truth-padding machine was obtained.** A low compiler score is a candidate for subsequent source and physical verification; it is not a consistency theorem or a lower bound.

## Completed experiments

| Experiment | Proposals scored | Best nominal state count |
|---|---:|---:|
| Duplicate complete ordinary axiom heads | 2,000,000 | 198 |
| Insert redundant truth entries, original controller | 4,000,000 | 195 |
| Initial boundary-insertion census | 97,361 | 195 |
| Reassociate AX in the new shared forest, including fixed/reader folds | 5,000,000 | 194 |
| Truth padding in the new shared forest | 5,000,000 | 195 |
| First-head implicational formula contexts | 3,000,000 | 201 |
| Neutral rotations around the new forest | 400,000 | 194 |
| Neutral rotations with truth padding | 600,000 | 195 |
| Further neutral rotations allowing all context-qualified controls | 800,000 | 194 |
| Direct-top/parameterized generalizer diagnostic | 6,959 | 195 |

These are proposal counts. Some families overlap, especially the two neutral searches; they must not be summed as a count of distinct Turing machines. The exact counters, seeds, accepted moves and layout exclusions appear in `summary.json` and the retained logs.

## Preserved source changes

`padding_preservation.tex` proves a general all-store command theorem for inserting zero theorems at completed AX-head boundaries. The ten-entry theorem list becomes an L-entry list, where L=10+n for n inserted zeros. Push, Pop, selectors and generalization have explicit adjusted command words. Cantor-stack zero aliases are included. The proof concerns the command interface; the searches did not find a qualifying physical implementation of the new protocol.

The first-head search replaces h1(D,H) by h1(D,F(A,H)), using the first head's otherwise unused parameter A. Each of its 241 contexts has either A=H or A=0 as a displayed specialization for which F is propositionally equivalent to H. The new heads are old axiom instances. Conversely, fixed propositional proof templates and quantifier congruence recover the old heads. The 482 seeds use the two inherited emitter shapes. The best score was 201, so no table from this experiment is presented as a new frontier machine.

The direct-top 188-token interface loses the saved incoming theorem and stores its universal generalization instead. Its carried-stack completeness remains open in the supplied packet. This experiment only prices its grammar in the new forest. It is explicitly not an accepted consistency machine.

## Scoring and contexts

The original controller has 134 fixed controls. The new shared forest has 136 and exposes the additional native macros `(node55,node65)` and a right-associated three-increment pattern. Its unused four-increment shortcut is removed from the scorer. `global_search/leaf_attrs.txt` is calculated from the new source trees, rather than reused unchanged from the old controller.

`screen_full.cpp` considers both fixed and AX reader controls, while excluding the inherited arithmetic-box interface. It admits a predecessor-bit context only when every incoming transition establishes that context. Every selected fold is checked simultaneously on its four applicable two-cell cases. The frontier score uses a maximum compatible set, rather than assuming independently valid folds compose.

`screen_all.cpp` broadens the context test to the bit *written* by each right-moving ingress, and permits the arithmetic-box controls too. The blank start is explicitly assigned predecessor bit zero. Such a fold would require the whole-table local transfer theorem; an unchanged-box oracle cannot certify a modified arithmetic box. No improving fold was obtained, so no delivered machine relies on this extension.

## Reproduction from captured inputs

The search inputs are self-contained; these commands do not require a repository checkout. They require a C++17 compiler. The final numeric parameter is the fixed proposal cap. A very large wall-time cap avoids a hardware-dependent early stop.

```sh
g++ -O3 -std=c++17 search.cpp -o search
./search duplicate.templates.txt leaf_attrs.txt duplicate_replay 1000000000 9911 2000000
./search padding.templates.txt leaf_attrs.txt padding_replay 1000000000 9912 4000000

g++ -O3 -std=c++17 global_search/search_full.cpp -o search_full
./search_full global_search/original.templates.txt global_search/leaf_attrs.txt original_replay 1000000000 9916 5000000
./search_full global_search/padding.templates.txt global_search/leaf_attrs.txt padding_replay 1000000000 9917 5000000
./search_full global_search/h1_context.templates.txt global_search/leaf_attrs.txt context_replay 1000000000 9918 3000000

g++ -O3 -std=c++17 global_search/neutral.cpp -o neutral
./neutral global_search/original.templates.txt global_search/leaf_attrs.txt neutral_replay 400000 1000000000
./neutral global_search/padding.templates.txt global_search/leaf_attrs.txt neutral_padding_replay 600000 1000000000

g++ -O3 -std=c++17 global_search/neutral_all.cpp -o neutral_all
./neutral_all global_search/original.templates.txt global_search/leaf_attrs.txt neutral_all_replay 800000 1000000000
./neutral_all global_search/direct_top.templates.txt global_search/leaf_attrs.txt direct_top_replay 200000 1000000000
```

The direct-top frontier exhausts after 6,959 scored neighbors, before the supplied cap. Runtime seconds may differ in every replay. The proposal sequence and score counters should remain the same with the same compiler's standard-library behavior; equal-score sorting and hash-table implementation details can affect a replay across different C++ implementations. The saved evidence records the actual observed runs.

Run the displayed commands from this `source_math/` folder. All templates needed for those search replays are included. The Python generators document how the captured inputs were prepared. Their small dependencies are frozen under `inputs/`: the two AX11H starting grammars and seed file, the selected shared-forest table and source nodes, and the two supplied parameterized-generalizer grammars. They use paths relative to the script, without depending on the original research workspace.

The two corpus-wide generators, `make_many_padding.py` and `make_global_search.py`, additionally require the pinned repository grammar corpus. Set `PROVEIT_ROOT` to a checkout of the stated commit before running them. They fail explicitly if that dependency is absent. `make_global_search.py` also requires the large `many_padding.templates.txt` produced by `make_many_padding.py`. This 97,361-tree census input is omitted here; its per-tree scores and the eight selected 195-state padding grammars are retained. Corpus regeneration is optional and is not part of the self-contained captured-input replay commands above.

`provenance/portable_inputs.json` records the frozen generator inputs and packaging changes. `provenance/original_curated_SHA256SUMS` preserves the manifest before the portability edits; the top-level `SHA256SUMS` covers the delivered folder. The edits affect dependency paths and provenance, not the captured template files or C++ search algorithms.

Repository snapshot: `VladimirReshetnikov/ProveIt` at `7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`. See `NOTICE.md` for inherited code attribution.
