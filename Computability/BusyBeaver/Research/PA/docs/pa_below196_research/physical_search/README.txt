PA196 local synthesis extensions, 13 November 2026
================================================

Status
------
No smaller machine is established by these experiments. The wider local
screen and the displaced-state screen completed with zero survivors. The
shared-row three-edit screen is reported only to the extent shown by its
receipt; a partial receipt must never be called an exhaustive all-pair result.
None of the searches proves a general lower bound on 195-state machines.

Pinned input
------------
Repository: VladimirReshetnikov/ProveIt
Commit: 3268f238cb6be4b9c68b6cddaf289f173f77566e
File: Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/data/pa196.tm
SHA-256: e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8
Working states 0..195, start 0, separate halt 196; binary, two-way tape.

The existing two-helper search is in ProveIt's pa196-vs-u208/search/two-helper.
scan_wide.cpp adapts that search by changing the active radius from two to
three and the maximum child block length from 16 to 32. Its inputs are a
stronger projection of the same radius-six blank-start abstract closure.
This is a seven-cell, not a thirteen-cell, endpoint screen. The thirteen-cell
closure contains 270,067 state/windows; its seven-cell projection has 8,120.
The input invariant has an abstract route to halt. Its closure cannot prove
nonhalting; its purpose is only to cover every concrete blank-start window.

Completed wider screen
----------------------
Ordered merged-state pairs:               38,220
First-row locations:                    125,092
First-row assignments:               98,072,128
Second-row locations:                 1,018,338
Second-row assignments:             798,376,992
Unpatched / one-row / two-row survivors: 0 / 0 / 0

The candidate must match every parent step by a positive child block with the
same projected state, head, and entire window. Reads stay inside seven cells
and each block lasts at most 32 transitions. Two arbitrary retained rows may
change; all references to the deleted state are projected to the keeper.
Necessary visited-row pruning is inherited from the cited two-helper screen.
The numbers count assignments examined by that algorithm, not nonisomorphic
machines. They do not exclude a larger block or a different representation.

A genuinely different representation: displaced state identification
-------------------------------------------------------------------
Let p be the state to delete, k the keeper, and s either -2 or +2. Define

  Phi(q,h,tape) = (k,h+s,tape) if q=p;
                 (q,h,tape)   otherwise.

Require every external incoming edge to p to have direction d with d+s in
{-1,+1}. Consequently s=-2 permits only right incoming moves, and s=+2 only
left incoming moves. Self-edges of p need not satisfy the condition because
p's two rows disappear from the child. For every remaining original row
whose target is p, redirect its target to k and change its direction from d
to d+s. Keep its write bit. Other remaining rows are unchanged. An additional
arbitrary helper-row replacement is permitted.

For an unpatched original state q different from p, this changed row performs
exactly Phi of the original step in ONE transition: both heads initially
coincide, the write remains in the same cell, and the head offset at target p
is supplied by the changed direction. Therefore only parent configurations
at p or at the patched helper need multi-step checks.

scan_offset.cpp checks every such configuration in the radius-six abstract
closure, using a positive child block of at most 32 steps confined to its
thirteen cells. Initial child head is s at p, and zero at the helper. The
expected final head is original d plus s iff the original target is p. All
thirteen tape cells must agree at the endpoint. The algorithm intersects
visited-row sets over failed unpatched runs to enumerate every possible
single helper row within this template. It then checks every legal write,
move, and retained-or-halt destination and all contexts at both p and helper.

Completed displaced screen:
  Eligible (p,k,s) choices:             33,735
  Possible helper-row locations:       47,684
  Replacement triples examined:    37,384,256
  Unpatched / patched survivors:       0 / 0

The 33,735 choices equal 173 eligible deleted states times 195 keepers.
This is only the uniform-external-entry family, not all displaced simulations.
If the deleted state is the initial state, Phi starts at head s on blank tape;
translation invariance identifies that with the ordinary head-zero start.

Why a successful finite certificate would suffice
------------------------------------------------
The abstract closure is checked for initial inclusion and transition closure.
Induction therefore puts every original blank-run window in the admitted set.
A checked local block preserves the entire tape because it does not read or
write outside its window and ends with identical window contents. At other
states, the projected transition commutes in one step. Induction over the
parent run yields a sequence of positive matching child blocks. No child
block may halt before its endpoint. A parent halt yields a child halt, and
an infinite parent run yields infinitely many child transitions because the
blocks are positive. Determinism rules out a different child behavior.
This gives halting equivalence for the transformation. It would not by itself
supply PA196's missing internal consistency-to-nonhalting implication.

The witnesses and all counts here are external finite computations, not newly
kernel-checked Lean or PA declarations. The finite invariant and bounded
block arguments are suitable for arithmetization; no exported internal proof
is included or claimed.

Full three-row synthesis on a restricted pair set
------------------------------------------------
scan_three.cpp does not use the earlier archive's representative-only third
row extension. For a failed current candidate, every successful completion
must alter a row visited on that failed trace. With two or three edits left,
the recursion chooses one shortest failed visited-row set and branches on
each remaining row and each non-no-op assignment. With one edit left, it
intersects visited-row sets over ALL failures. Every newly patched helper
state is added to the universally checked parent contexts.

This recursion is complete for at most three changes for its selected state
pair, five-cell contexts, and 16-step blocks. It skips replacements identical
to the projected base row, which cannot change any execution. It can visit
multiple orders of the same patch set; counters count search assignments.
The 348 ordered pairs selected for the larger run share at least one literal
outgoing row in the original table. This restriction is part of the scope.
It does not exhaust all 38,220 pairs under the three-row template.

Independent positive controls
-----------------------------
replay.py contains a separate dictionary-tape implementation that checks the
known two-helper synthetic fold on all 512 seven-cell parent contexts and a
genuine displaced fold on all 160 five-cell parent contexts. In the latter,
five working states have preserve-symbol/right transitions with targets
0->1, 1->3, 2->halt5, 3->halt5, 4->2. Delete 2 into 0 with offset -2 and
reverse both incoming state-4 moves. The parent step at 2 is replaced by
three child steps, with the full tape unchanged. scan_offset.cpp recovers
exactly the unpatched witness PLAIN 2 0 -2 on those supplied contexts.
The three-row engine recovers the original synthetic two-helper witness.

Reproduction
------------
  python3 replay.py /absolute/path/to/pa196.tm --output receipt.json
  python3 replay.py /absolute/path/to/pa196.tm --shared-three --workers 4 \
      --output full_receipt.json

The default command recomputes and separately audits abstract closure, runs
independent positive controls, and repeats the wider and displaced searches.
The optional shared-three run can take much longer. No network or third-party
Python packages are needed; g++ with C++17 is required.

Attribution
-----------
scan_wide.cpp derives from ProveIt's two-helper/scan.cpp at the pinned commit,
under the repository's MIT No Attribution license, retained as LICENSE.ProveIt.
The literal PA196 table itself is James Chang's machine; its original license
must accompany a redistributed table. The recursive three-row and displaced
engines and independent controls were written in this research session.

Frozen partial three-row result
-------------------------------
The shared-row run completed 84 of its planned 348 ordered pairs before
research attention moved to source specialization. The exact completed pairs
are listed in partial_three_receipt.json. Across those pairs it examined
162,081 first, 328,246,128 second, and 9,582,125,364 third-row assignments,
with zero survivors. This is NOT an exhaustive result for the 348-pair set.
