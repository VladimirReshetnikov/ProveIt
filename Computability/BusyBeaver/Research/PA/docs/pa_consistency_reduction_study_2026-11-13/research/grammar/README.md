# Grammar, negation and scanner experiments

These are discovery experiments. **None produced an accepted sub-194 consistency machine.** Sources descend from the pinned repository's `pa194n6_research_2026-11-13/research` search machinery, with the new objectives and input variants described below.

## Standalone C++ runs

All inputs and included C++ sources are adjacent. Build with a C++17 compiler. The final numeric arguments are seconds and the random seed. Logs from the original runs are retained; use a fresh output prefix for reruns.

```sh
g++ -O3 -std=c++17 neg_anneal.cpp -o neg_anneal
./neg_anneal neg_seeds.txt neg_attrs.txt rerun_neg 600 141127

g++ -O3 -std=c++17 scanner_anneal.cpp -o scanner_anneal
./scanner_anneal neg_seeds.txt neg_attrs.txt rerun_scanner 600 141129

g++ -O3 -std=c++17 short_anneal.cpp -o short_anneal
./short_anneal short_seeds.txt short_attrs.txt rerun_short 600 141128

g++ -O3 -std=c++17 bin_grammar.cpp -o bin_grammar
./bin_grammar neg_seeds.txt short_attrs.txt milp_productions.txt rerun_bin 120 141130
```

`screen.cpp` supplies the transition and fold machinery; `search_plateau.cpp` is included by `bin_grammar.cpp`. Search scores use reader count minus a fold bound plus the documented context/scanner penalties. A score does not replace reconstruction and simultaneous fold, whole-program runtime, logical and startup checks. Runtime-limited iteration counts vary between machines.

### Alternative negation

Eight eligible macro fragments of the form `node49, inc T, node65` can be replaced by `inc Y, inc Y, node64`, using an existing 18-instruction arithmetic implementation. `neg18_screen.json` records all 256 choices for each of the primary and Q inherited associations. The lowest optimistic effective-reader count is 60, so no inherited-association improvement is exposed.

`neg_anneal.cpp` also changes binary associations and occasionally parameter permutations. It completed 10,430,534 proposals in 600.001 seconds, with 1,859,186 accepted proposals, zero hits, and best score 60. The 134-state fixed part therefore was not improved below the 194-state frontier by this run.

`scanner_anneal.cpp` charges additional scanner controls when a longer maximum zero run requires them. It completed 9,700,610 proposals in 600.003 seconds, with 2,782,603 accepted proposals, zero hits, and best score 60. No proposed hit warranted construction of the extended physical scanner.

`neg18_screen.py` is the exhaustive substitution driver. It requires the pinned checkout and its compiler/runtime modules. Set `PROVEIT_REPO` to that checkout. The packaged version changes only the paths so outputs are written beside the script:

```sh
PROVEIT_REPO=/path/to/ProveIt python3 neg18_screen.py
```

### Preliminary shortened-scanner run

`short_anneal.cpp` imposes maximum address-zero run five and pre-increment zero run four. Its 600-second run examined 11,787,742 proposals, accepted 1,225,008, found zero hits, and retained best penalized score 64.

This preliminary instance is deliberately **not** a complete physical shortened-scanner model: its fixed input does not repair the root rotation's history-sharing and bootstrap obligations. It is retained as a source-discovery experiment, not a lower bound or a candidate machine. The later exposed-helper experiment in `../zfc_transfer/` models the history reader explicitly and also found no admissible hit.

### Dictionary optimization and binarization

`min_grammar_extended.py` expands the primary macro word while permitting existing free `inc2` and `inc4` macros, and minimizes the summed `len(rhs)-1` cost of a repeated-substring dictionary. It needs NumPy and SciPy. The input `primary.grammar.json` is included.

```sh
python3 min_grammar_extended.py
```

The first 1,200-second-budget run was terminated by the environment before completion; `grammar_solver.log` is an incomplete run, not negative evidence. A subsequent 600-second-budget, single-threaded run completed after 359.956970216 seconds. HiGHS reported objective and bound `66.99999999999977`, with zero gap. The returned dictionary has 25 reachable productions and exact integer cost 67.

The feasible word and cost are independently checked by the archive's standard-library grammar verifier. No exact dual or branch-and-bound certificate for **optimality** is supplied for this dictionary problem. Its optimum is a solver report. This objective omits physical scanner constraints, compatible reader folds, and initialization.

`bin_grammar.cpp` tries binary associations of that fixed dictionary. Its 120-second run examined 2,440,263 associations and achieved best penalized score 69; no accepted machine resulted. The retained best grammar is a scored search object, not a physical table.

## Files and limits

The input text instances contain the fixed transition rows, terminal macro attributes and complete seed trees. Saved seed grammars and logs allow continuation or analysis without reproducing input generation. `../search_summary.json` records the completed runs in a compact form. Time limits, chosen representations and penalties restrict these searches; none proves global optimality or rules out a new 193-state construction.
