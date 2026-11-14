# Discovery of the 194-state construction

These searches are optional research artifacts. They do not form part of the
certificate checker for the delivered 194-state construction. No negative
search result below establishes a lower bound on the size of a PA-consistency
machine.

## Compatible-fold grammar searches

`search_exact.cpp` and `screen.cpp` are the exact-compatible-fold search from
the supplied `PA195_ConPA_research_2026-11-14.zip`, copied with its original
attribution and licenses retained in the main package. `search_plateau.cpp`
is a modified search that selects among the best 30 current pool entries,
uses a lower temperature, and admits pool entries only through score 62.
The search fitness is the number of AX reader states after compatible local
folds, with scanner penalties. The fixed part contains 134 states; score 60
would therefore be a prospective 194-state construction, still requiring
the complete source and tape verification.

Three searches with 600-second budgets start respectively from the supplied separated
195-state tree, the supplied diagonal 195-state tree, and the new cross
tree obtained by deleting the final outer `cons`. A fourth search with a 400-second budget
uses the modified search on the separated tree. The input files contain the
fixed table rows and numeric tree structures; `leaf_attrs.txt` provides the
scanner attributes. They need no external source checkout. The first two
runs completed their budgets. The cross run and the modified run were
stopped after the 194-state candidate had passed its complete symbolic and
startup verification; their final iteration counts are not asserted.

The modified search found the retained 194-state grammar at proposal
4,454,453, after 229.826 seconds of that run. It has 67 raw AX readers and
seven compatible folds, giving `134 + 67 - 7 = 194`. All six parameter
permutations are the identity (`000000`), so the entire 190-token word and
the resolved 3,673-instruction source graph are unchanged. The frozen
`winning_grammar.json` is identical to the primary construction input.

Example commands, from this directory:

```sh
g++ -O3 -std=c++17 search_exact.cpp -o search_exact
./search_exact inputs/separate.txt inputs/leaf_attrs.txt separate 600 2026111401
./search_exact inputs/diagonal.txt inputs/leaf_attrs.txt diagonal 600 2026111402
./search_exact inputs/cross.txt inputs/leaf_attrs.txt cross 600 2026111403
g++ -O3 -std=c++17 search_plateau.cpp -o search_plateau
./search_plateau inputs/separate.txt inputs/leaf_attrs.txt plateau 400 2026111404
```

Runtime-limited stochastic searches will not reproduce the same proposal
counts on different computers. The saved logs record the actual runs;
`summary.json` records their outcomes. Candidate grammar fitness is a search
filter, not the full mathematical correctness test.

## Longer local detours and sequential quotients

`action_merge.cpp` computes an overapproximation of reachable nine-cell
windows (radius four) from native start state 74, allowing every initial
tape. Its finite abstract transition relation shifts the window and allows
either new boundary bit. For each control/read pair it tries every possible
first action whose next control is an existing working control, then follows
the current table for at most 80 transitions, entirely within that window.
The endpoint must reproduce the old single transition's control, head
position, and complete window. Intermediate paths must avoid the controls
whose rows are being changed. Shared valid first actions on both read bits
give a sufficient local quotient certificate. Arithmetic-box controls are
excluded as removed states and keepers.

`search_quotients.py` closes this specific rewrite rule under repeated
application, starting with an unfolded source table. It considers all
reported first-action combinations, uses exact table hashes to deduplicate,
and records the number of pending tables when it finishes. It does not claim
to enumerate every correct local or global state reduction.

```sh
g++ -O2 -std=c++17 action_merge.cpp -o action_merge
python3 search_quotients.py inputs/cross202.native.tm quotientcross 10000
python3 search_quotients.py inputs/separate201.native.tm quotientseparate 10000
```

The cross family closes after 192 distinct tables, with best size 195; the
separated family closes after 144 distinct tables, with best size 195. Both
queues are empty at completion, so neither 10,000-table cap was reached.
These counts concern this defined finite local rewrite system. An additional
helper detour using native state 190 was found, but it did not lead below 195.

`local_merge.cpp` is the narrower preliminary experiment that keeps both
rows of the receiving state unchanged. Its absence of candidates on the
folded 195-state tables was superseded by the broader action search.

The optional fourth argument to `action_merge` or `local_merge` after the
step bound is a context file containing `state bitmask` pairs. Bit zero is
offset minus the radius; the center bit is at the radius. Supplied states
replace their abstract windows; omitted states retain the general abstract
windows. Such a restricted context file needs a separate justification.
The two sequential-quotient runs above do **not** use that option.
