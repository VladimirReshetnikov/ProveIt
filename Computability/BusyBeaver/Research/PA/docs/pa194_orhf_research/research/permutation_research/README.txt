Exact finite register-allocation/fold screen

All 9!=362880 bijections of the nine physical register slots were enumerated
on the pinned 201-control unfolded primary PA194 table. Each assignment
changes the targets of the 11 non-engine marker-selector rows. The nine
marker engine controls themselves remain fixed. A fold is individually
eligible when its incoming rows preserve a known predecessor bit and a
1/3-step two-cell provider implements its differing transitions. All eligible
non-box controls are considered, rather than only the 67 AX reader controls.

The maximum bipartite matching size in that graph is exactly 7 for every
assignment. This matching is an upper bound on a simultaneously valid set
of these folds: no claim is made that every selected matching is compatible
after all rewrites. An upper bound below 8 already excludes a 193-state table
obtained from this 201-state parent by 8 disjoint folds of this exact template.
It excludes neither longer detours nor larger windows, altered source
programs, multiple interacting rewrites, or other Turing machines.

The smaller first run enumerated all 40,320 assignments fixing physical slot 6
and reached the same result. The later full run supersedes its scope.

Reproduce with a C++17 compiler:
    g++ -O3 -std=c++17 permutation_folds.cpp -o permutation_folds
    ./permutation_folds unfolded201.native.tm >hits.jsonl 2>log.txt
Optional slot 6-only run: append any second argument, such as fixed6.
The supplied full log and receipt contain the exact completed counts.
This search is deterministic and exhaustive within the stated finite family.
