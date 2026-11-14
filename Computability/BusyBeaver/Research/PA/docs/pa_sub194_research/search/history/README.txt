TWO-CELL HISTORY-REPAINTING SEARCH

Result: 43 distinct 194-state action graphs, 177,936,788 branch-action
proposals, no surviving pair of replacement rows. This is a scoped finite
negative search, not a lower bound on Turing machines. The input collection
includes 28 reported constructions, 10 auxiliary graphs and 5 rejected
graphs; a reduction of a rejected graph would not establish Con(PA).

Template: incoming transitions to two merged controls all move right and
each writes a fixed bit. Those old bits may agree. Rewrite the incoming
writes to distinct control tags 0 and 1; merge the controls; use existing
helpers to restore the original preceding bit and simulate the old action.
Each candidate branch is one original action or a move-left action to an
existing helper. Exhaust all four (old control, current bit) cases.
Only the two cells at head offsets -1 and 0 may be read before the exact
parent successor is reached, within nine child transitions. Recursion
through the new merged branch is excluded. Neither merged control may be
the designated start. Incoming edges from the merged pair are excluded.

Replay, from this directory:
  python3 check_controls.py
  python3 repaint_fold.py ../../references/frontier_tables/*.tm --output replay.json

All supplied frontier tables are densely relabeled with working controls
0..193. They are graph-comparison representatives. The search protects
their control 0; it does not infer consistency from their graph identity.
The helper fixture demonstrates a three-step restoration and its corrupted
negative control. It does not formally verify the search implementation.

repaint_frontier.json is the completed search receipt. repaint_controls.json
is the original control receipt. The additional unconditional_repaint.json
records only a diagnostic search on two altered, non-certified parents
with a 17-step bound. It is not counted in the main 43-input result and
does not establish a consistency-machine construction.

FINAL MP196 SCREEN
The frozen new 196 table was also checked with the same template and a
17-step bound: 107 eligible controls, 4,373,528 branch-action proposals, 0
survivors. The record is mp196_repaint.json; input is the main native table.
It is separate from the 43-input frontier result.
