PHYSICAL REDUCTION RESEARCH
===========================

Result: no additional sub-194 blank-start consistency machine was established.
research_summary.json is the definitive compact results ledger. SEARCH_NOTES.txt
gives the exact two-edit bootstrap experiment, limits and detector semantics.
The runtime193.native.tm file is the PRE-EXISTING REJECTED blank-start candidate;
it is an input to repair research, not a claimed new consistency machine.
The gh_input/ files are the exact new PA194GH source/table used by these searches.

This folder is offline and self-contained. Python3.10+ and a C++17 compiler suffice.
Run commands from this folder. No proof assistant is required for these executable
screens, and no proof-assistant theorem is claimed.

CORE REPLAY COMMANDS
-------------------
g++ -O3 -std=c++17 search_pairs_cycles.cpp -o search_pairs_cycles
./search_pairs_cycles runtime193.native.tm neutral.tsv any_frames.tsv 200000 1

g++ -O3 -std=c++17 search_triples.cpp -o search_triples
./search_triples runtime193.native.tm neutral.tsv any_frames.tsv 200000

g++ -O3 -std=c++17 allocation_quotient.cpp -o allocation_quotient
./allocation_quotient pa194.native.tm 1

python3 restore_skip_search.py

g++ -O3 -std=c++17 coupled_repair_fast.cpp -o coupled_repair_fast
./coupled_repair_fast runtime193.native.tm witnesses.txt 88 122 10000
./coupled_repair_fast runtime193.native.tm witnesses.txt 88 51 10000

python3 liveness.py

GH LOCAL QUOTIENT REPLAY
-----------------------
python3 collect_source_contexts.py gh_input/machine.native.tm \
  gh_input/sites.json gh_input/instructions.json gh_patterns_k4.txt 4
python3 collect_source_contexts.py gh_input/machine.native.tm \
  gh_input/sites.json gh_input/instructions.json gh_patterns_k6.txt 6
g++ -O3 -std=c++17 joint_return_merge.cpp -o joint_return_merge
./joint_return_merge gh_input/machine.native.tm 4 100 gh_patterns_k4.txt
./joint_return_merge gh_input/machine.native.tm 6 200 gh_patterns_k6.txt

g++ -O3 -std=c++17 neutral.cpp -o neutral
./neutral gh_input/machine.native.tm 6 200 gh_patterns_k6.txt > gh_neutral_k6.jsonl
python3 gh_neutral_quotient.py

Interpretation: the source contexts include every prescribed source outcome and
interior positions skipped by constant-symbol loop acceleration. Arithmetic-box
interiors are not narrowed by the collector. The contexts intentionally exclude
blank startup. A positive local candidate would need universal refinement and an
exact startup connection before it could be claimed as a consistency machine.
The eight neutral-followed-by-quotient screens reuse the original GH context
envelope; they are not an exhaustive sound two-edit transformation calculus.

LIVENESS LIMIT
--------------
The seven loops summarized as r:=0 are exact decrement/unconditional-jump loops.
The0/positive abstraction then reaches263,132 abstract states. Syntactic liveness,
intersected with the possibly-positive registers, contains a complete9-register
interference graph. This rules out direct static8-coloring under this abstraction.
The explicit abstract witness is not claimed to be a concretely realizable run.
More exact relations, alternate command algorithms, and packed counters remain open.

INTEGRITY AND PROVENANCE
------------------------
sha256sum -c SHA256SUMS
PROVENANCE.json identifies inherited code/data, new scripts, and original licenses.
Files ending in .log.txt or .json are frozen receipts. Timing fields depend on host.
