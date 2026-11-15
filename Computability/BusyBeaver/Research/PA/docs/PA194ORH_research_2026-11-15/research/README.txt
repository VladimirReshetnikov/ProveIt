NEW REDUCTION RESEARCH
======================

All negative results here are scoped experiments, not a global state-count
lower bound. Accepted machines are in ../machines/. This directory also
retains deliberately failed 193-state candidates and an auxiliary195-state
new protocol; their status must not be confused with the principal result.

reader_search/: 135 fixed controls including the repaired operand selector
and shared (CopyD, constructor) reader; target effective AX count58 for193.
expanded_search/: additionally exposes Push+copy internals of CopyD/H/A
and lets the AX grammar share their preinstalled pairs.
Both retain portable C++ source, screen.cpp, frozen seeds and attributes,
search.log, and a JSON receipt. Run from the respective directory:

  g++ -std=c++17 -O3 search.cpp -o search
  ./search seeds.txt leaf_attrs.txt run 300 193194

The expanded run used seed194193; ordinary used193194. The last two arguments
are a wall-time budget in seconds and a random seed. Wall-time-limited runs
are not byte-reproducible across processors; retained logs give the actual
proposal totals. Ordinary:1,780,509 proposals; expanded:2,484,415. Both best59.
Code is adapted from the inherited shared-DAG search in the revised AX11H
research, with the documented fixed reader and copy expansions. Its licenses
are retained in ../licenses/ and logical search provenance under logic/.

beam_results/summary.json: 1,277 priced source-preserving tree/return
reencodings, including two nominal193 candidates rejected by physical checks.
return_results/summary.json: 17,399 shapes,55 admissible source-preserving
small-routine encodings (at most ten leaves), no193.
commute_results/summary.json: 182 unique variants combining independent
increment swaps and closed-routine rotations, minimum nominal195.
These three directories are recorded search data. Their original exploratory
drivers depended on the source checkout; they are not advertised as standalone
replay scripts. The key rejected193 mechanism has a complete portable replay
under engine/.

REJECTED193_operand/: full retained false193 table/source/folds and the
30 failed outcomes; its source graph and local folds alone do not establish
physical correctness. engine/check_rejected.py replays the decisive failure
from the equivalent retained engine fixture, plus the scanner counterexample.

engine/README.txt and logic/README.txt describe all other searches and checks.
