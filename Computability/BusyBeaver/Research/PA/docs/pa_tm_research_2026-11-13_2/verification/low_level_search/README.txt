PA196: valid zero-jump substitutions and scoped state-fold searches
================================================================

Result
------
No 195-state machine was found in the recorded finite template.  This is a
negative search result, not a lower bound on the size of a PA-consistency
machine.  Both supplied parent tables still have 196 working states.

The parent tables differ from the pinned jamesyc PA196 table only in the
transition on symbol 1 at native state 27.  They implement source site 26,
whose original instruction is a forward jump CB1, by decrementing a
register proved zero at that source site:

  cd6_parent196.tm: native27/1 becomes 1 R 21 (logical CD6).
  cd3_parent196.tm: native27/1 becomes 1 R 17 (logical CD3).

The tables use dense labels 0,...,195 and halt label 196; initial label is 0.
The CD6 table reaches the original initialized source frame after exactly
58,402 blank-tape transitions.  The source invariant has 274,880 pairs
(source instruction ordinal, nine-bit zero/positive mask).  Its derivation
and all symbolic register-instruction contracts are included in the context
generator.  For the CD3 runtime and startup checks, use the accompanying
zero-jump substitution certificate in the complete research package.

What was searched
-----------------
For every ordered pair of distinct working states, delete the first and
identify it with the second, redirecting every incoming transition.  Permit
at most two arbitrary changes to retained transition rows.  Every affected
parent transition must match a positive block of at most 16 child steps,
with equal projected control, equal head position, and equal contents of
all five cells at coordinates -2 through 2.  The block may not read beyond
these five cells.  The C++ search uses necessary visited-row conditions to
prune candidates without omitting any member of this finite template.

The inputs to each search are conservative sets of permitted local windows.
The global windows come from a radius-six inductive blank-start abstraction
that freely chooses each newly exposed boundary bit.  The source windows
come from uniform symbolic instruction contracts with unbounded register
values, an unbounded header gap, and an arbitrary finite spare-register
list, plus the exact finite startup and conservative list-interior windows.
The final file intersects these two sound overapproximations.

The mask variant additionally imposes every source register that is always
zero or always positive in the full 274,880-pair invariant.  It skips the
two unreachable source sites and one unreachable decrement branch.  It
uses the per-coordinate consequences of that invariant, not all remaining
correlations between uncertain register values.  Its 2,221-window output
is byte-identical to the earlier universal-source window output.  The
completed search therefore applies unchanged to both files.

Recorded results
----------------
                         ordered folds   second-row choices   survivors
  CD6, global windows       38,220          419,247,136             0
  CD6, source windows       38,220          573,273,344             0
  CD6, source-mask windows  same file and same completed search    0
  CD3, global windows       38,220          409,988,096             0

These choice counts are the candidates that remain after sound pruning;
they are not counts of all conceivable Turing machines.  The JSON receipt
records all input hashes, exact counters, and scope limitations.

Reproduce
---------
Python 3 and a C++17 compiler suffice.  From this directory:

  python3 verify.py

This checks the saved file hashes, exact CD6 startup, table shape, the
single-row modifications, and the equality of the two source-window files.
It also checks the saved search counters.  It does not rerun the search.

To regenerate the source-mask windows and rerun that finite search:

  python3 code/generate_contexts.py --output rerun_contexts
  g++ -O3 -std=c++17 code/all_folds.cpp -o all_folds
  ./all_folds inputs/cd6_parent196.tm rerun_contexts/source_contexts.txt rerun_survivors.txt 196 196

The generator performs 4,956 reachable symbolic contracts.  The recorded
run has 1,178,065 symbolic steps.  A rerun must produce context SHA256:

  ca13223d8d586e3a58a35396cd0688d0180896e1c963026bd646de04cbd48377

These are executable mathematical checks.  They are not Lean kernel
certificates.  The startup is a finite exact computation; unbounded tape
behavior is addressed by the symbolic contracts and inductive invariants.

Provenance
----------
Pinned repository:
  https://github.com/VladimirReshetnikov/ProveIt
  commit 1fe9b29810bfe3d0e507146d65f6b97692e7444a

Program.lean, Conjugacy.lean and the baseline table come from
Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/.
The symbolic runtime and source helpers are adapted from the sibling
pa196-vs-u208/source-search/allocator-screen/ and source-search/ modules.
The two-row synthesis screen extends the local-fold template supplied in
the incoming PA research archives.  Included license notices preserve the
ProveIt, James Chang, and Wade source attributions.
