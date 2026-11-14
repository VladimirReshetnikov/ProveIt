# Bounded decoder reductions with seven movable AX heads

No 193-state machine was obtained in these searches. The numerical screen
scores a finite decoder-allocation template. It does not prove a lower bound
on Turing machines, and a low score alone would not validate a machine.

## New search scope

The six ordinary unconditional AX heads and the separated diagonal head can
be permuted as seven complete blocks. Each block's three register parameters
can be bijectively renamed. The fixed 18-token prefix and 62-token suffix
remain unchanged; the entire macro word has 190 tokens. Local occurrence
rotations and simultaneous rotations of equal subtrees vary the binary DAG.
The earlier six-head algorithm is retained by attribution in PROVENANCE.json.
Earlier packets also examined seven-head permutations in fixed shapes; the
new runs combine this degree of freedom with ongoing reassociation.

The PA194H6 screen additionally borrows native control 330, already present
in its radix-six multiplication routine, to read three literal increments
as `(incT,(incT,incT))`. Its screen permits compatible contextual folds
involving eligible fixed controls as well as AX readers. The two-cell fold
sets are checked simultaneously by the scoring code. The coefficient-six
core contains 135 controls, so a screen score at most 58 would be needed
for a 193-state candidate. Primary and cached coefficient-four cores have
134 controls and need a score at most 59.

`summary.json` gives exact completed-run counters. A proposal slot need not
represent a new grammar or even reach the numerical scorer. Wall-clock
budgets make replay counts dependent on the machine and its load. Recorded
counts are not exhaustive search bounds.

## Reproduce

Compile with a C++17 compiler, from this directory:

```sh
c++ -O3 -std=c++17 seven.cpp -o search
c++ -O3 -std=c++17 seven_aggressive.cpp -o search_aggressive
c++ -O3 -std=c++17 seven_h6.cpp -o search_h6
./search seeds.txt leaf_attrs.txt replay_original 480 202611142310
./search seeds_cached.txt leaf_attrs.txt replay_cached 480 202611142311
./search_aggressive seeds.txt leaf_attrs.txt replay_aggressive 360 202611142317
./search_h6 h6seeds.txt h6attrs.txt replay_h6 360 202611142319
./search_h6 h6_gammaD.txt h6attrs.txt replay_h6_gammaD 240 202611142322
python3 check_saved_grammar_words.py
```

The last command checks that every saved grammar belongs to the exact
seven-head mutation domain. It checks source words, not physical execution.
The gamma-D seed deliberately starts with the diagonal schema using register
D; the same axiom instances remain available by the AX parameter enumeration.

The search preserves the supplied scanner-height constraints as a scoring
penalty. A zero-penalty numerical candidate would still require exact source
resolution, a new proof-word compiler for its head order, a complete literal
physical audit, and exact blank initialization. No below-194 candidate
passed even this first numerical screen, so no such acceptance is claimed.
