Runtime193 bootstrap search (negative result)
============================================

This directory records a fresh adaptive search for blank initialization of
the incoming runtime193 core. It does not contain an accepted 193-state machine.

The core is copied, byte for byte, from the runtime193 directory of
docs/incoming/pa_sub194_research_2026-11-13.zip at ProveIt commit
2337ce611a26e308697ccbddb2a1636f989f01c3. The 346 proposed row substitutions
come from that packet's corrected radius-six context screen. That screen
contains 19 speculative arithmetic-box rewrites as well as 327 outside-box
rewrites. No simultaneous combination is assumed semantically valid.

The search explores only edits encountered on a run, deduplicating sets of
edits. It tests all 193 starts with at most two changes, and start 74 with at
most three changes. It recognizes whole-tape canonical frames at source
sites 25 through 44, with arbitrary registers and a nonempty spare list.
These are the candidate entry sites covered by this search.

No frame was found. Some runs end at the specified limits, so this is
bounded search evidence, not a proof that the tested tables all fail forever.
It is not exhaustive for all two-row or three-row rewrites: edits are drawn
from the given menu, and adaptive reachability constrains enumeration.

Reproduce with a C++17 compiler:

  g++ -O3 -std=c++17 compound.cpp -o compound
  ./compound runtime193.native.tm edits.tsv startup_any_frame_templates.tsv 2 200000 -1
  ./compound runtime193.native.tm edits.tsv startup_any_frame_templates.tsv 3 200000 74

The JSON receipt gives counts and bounds. The C++ program emits any found
frame to stdout and progress/counts to stderr. Empty recorded stdout means
no frame was detected. The scanner changes that define runtime193 are
discussed in the report; startup is precisely the unresolved obligation.
