Joint semantic AX11 / AX11H grammar search
=======================================

This directory records a bounded attempt to obtain one fewer working
state. It is a negative research result, not a state-count lower bound.
No completed iPRA consistency theorem is asserted by this search.

Scope
-----
Each controller was searched from 96 seeds:

  2 emitter tree shapes (original PA194 and Q),
  2 equality orientations,
  8 combinations of Curry exchange in logical heads 3, 4 and 6,
  3 choices of diagonal argument (A, D or H).

Every seed has the AX11 terminal stack push and no-push successful MP.
The H run additionally uses the exact AX11H fixed controller rows.
During annealing, each of the six unguarded logical heads may independently
permute its three argument registers; the guarded gate and restricted
implication head remain unchanged. Grammar rotations may affect one tree
occurrence or every occurrence of an interned subtree.

The independent parameter-surjectivity argument is in
parameter_preservation.tex. The equality conjugacy and Curry exchange are
inherited ideas, not claimed as new here. The new experiment combines
these semantic degrees of freedom with the terminal-push AX11 protocol
and, separately, the cached-only H guard.

Scores
------
A raw reader node costs one working state. The score subtracts a set of
compatible history folds checked together on their four two-cell contexts.
There are 134 fixed working controls in either captured input, so an
effective reader count of 60 means a 194-state candidate construction,
and 59 would be a 193-state candidate. Additional penalties screen known
scanner and return-path restrictions. Penalty zero is necessary, but is
not a substitute for the full source-contract checker and blank startup.

Both sets of 96 fixed seed scores appear in seed_scores*.csv. These score
tables are not claims that each seed implements its intended source; any
prospective winner would have to be rebuilt and verified independently.
For speed, simultaneous compatibility is checked only when the optimistic
matching score has at most 64 effective readers. Larger entries therefore
report an optimistic fold score, not a verified compatible folding. The CSV
marks this distinction explicitly. Every potential sub-194 hit falls well
inside the range where compatibility is checked.

Reproduction
------------
The captured seeds.txt and seeds_h.txt are self-contained: each contains
all fixed native transition rows followed by every emitter tree. Neither
the search nor seed scoring needs a repository checkout.

  g++ -std=c++17 -O3 score_seeds.cpp -o score_seeds
  ./score_seeds seeds.txt
  ./score_seeds seeds_h.txt
  g++ -std=c++17 -O3 search.cpp -o search
  ./search seeds.txt leaf_attrs.txt replay 300 141126
  ./search seeds_h.txt leaf_attrs.txt replay_h 300 141127

The last number is the random seed. The recorded runs used 300 seconds
each. Their endpoints depend on CPU speed. The supplied source also
accepts a final optional maximum-proposal count, so the exact random
prefix can be replayed by using a sufficiently large time budget and the
proposal count in results.json:

  ./search seeds.txt leaf_attrs.txt replay 1000000000 141126 COUNT

The fixed-count option was added after the recorded searches, without
changing their proposal or scoring logic. It does not change the random
prefix before a stopping condition is met. Runtime seconds and final
partial-cycle reporting can differ.

The generator make_seeds.py is included for regenerating the captured
inputs from the pinned repository and extracted AX11 archive:

  python3 make_seeds.py --repo REPO --primary AX11_PRIMARY
  python3 make_seeds.py --repo REPO --primary AX11_PRIMARY \
      --h-raw AX11H_RAW_NATIVE_TABLE --prefix seeds_h

Provenance
----------
The repository snapshot is
1c9524d8bf2e0a27b9a16ff622359927f536e663.
The inherited C++ scoring and joint-search engines are from
Computability/BusyBeaver/Research/PA/docs/
pa194q_conpa_2026-11-13/search/{screen.cpp,parameters.cpp}.
The leaf attributes are from the incoming
pa194_ax11_research_2026-11-14.zip packet's primary AX11 grammar search.
The search engine is changed only to use the 193-state reporting
threshold and the optional fixed-proposal stopping condition. The
96-seed generator, seed rescorer, run inputs, receipts, and preservation
note are new work in this request. See provenance.json for file hashes.

The companion restricted-rho files in the parent directory establish a
separate finite propositional obstruction. They do not establish any
machine reduction or general lower bound.
