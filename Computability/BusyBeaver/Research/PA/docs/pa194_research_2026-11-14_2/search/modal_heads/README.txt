COMPLETED MODAL FIRST-HEAD SEARCHES

This folder records unsuccessful but logically motivated experiments extending
the existing PA194 AX11H grammar search. It is research evidence, not an
additional certified consistency machine.

The accompanying TeX proves equivalence of two alternative first logical
heads, B and C, to the original head using the retained classical templates,
distribution, and theorem generalization. Each has the same 17 emitter tokens.

B and C were each combined with 96 semantic seeds: two equality orientations,
eight h3/h4/h6 premise-exchange choices, three diagonal parameters, and two
source-tree shapes. BG changes the saved generalization binder to the direct
AX operand in the 96 B seeds, plus one previously obtained best B grammar.
Every run permits associativity and unguarded-head register permutations.

RESULTS.json records exact counts, inputs, hashes, and replay commands. The
three runs performed 6,666,025 proposed changes, accepting 2,190,004. Their best
optimistic effective-reader counts were 65,68,65. With 134 fixed states these
correspond to optimistic totals 199,202,199. No <=194 design was obtained.
Those totals are not certificates of 199/202-state machines: for scores above 64
the screen uses a matching bound without proving simultaneous fold validity.
The results are finite searches and imply no global state lower bound.

To replay with the same proposal counts, compile the supplied C++ source with
  g++ -std=c++17 -O3 -DNDEBUG search.cpp -o search
then run each command in RESULTS.json. The large time cap makes the iteration
count the stopping rule. Logs differ in elapsed times. Portable statistical
claims are the archived observations; bit-for-bit trajectories depend on the
C++ implementation, especially unordered-container iteration and RNG library.
No binaries or large redundant intermediate seed grammars are included.

The search code and physical leaf attributes are adapted from the pinned
ProveIt commit's latest AX11H incoming packet (see RESULTS.json). The new
contribution is the first-head change, seeds, bounded run, and equivalence
argument. Upstream licenses are retained.
