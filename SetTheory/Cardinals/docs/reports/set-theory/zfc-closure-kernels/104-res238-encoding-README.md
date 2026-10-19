# A displaced-head quotient screen on the 238-state machine

This directory records an independent finite negative result. It is not a
premise of the accepted 238-state consistency machine, and does not establish
any state-count lower bound.

## New certificate family

The original local-fold searches compared checkpoint configurations with the
same head position. Here deletion of a state q may use the representation

    (q, h, T)  ->  (r, h+k, T),  where k is +2 or -2.

Every other state preserves its head, tape and label. Delete q only when all
its incoming transitions move in one direction d, q has no self-loop, and q
is not initial state 95. Set k = -2d. Every incoming edge then reverses its
move direction and targets retained state r, preserving its write bit.
These changes exactly preserve the representation after a transition from
any source other than q or r. Both rows of r are synthesized freely; all
other outgoing actions remain fixed except those mandatory incoming edits.

At old states q and r, compare positive blocks: at most 63 old steps and
127 new steps, without reading beyond the eleven-cell radius-five window.
An endpoint must have exactly the same entire window/tape and its head and
state must agree under the representation. The comparison allows an old
endpoint at q, so the representation is used recursively. Final head
positions outside the window are permitted only after a move with no
subsequent read there. No halt-tape relaxation is used.

For each input bit, enumerate every possible retained row (two writes, two
moves, any remaining working state or halt). A partial check may stop when
the opposite retained input is first encountered. Thus failure before that
point excludes the row regardless of the other row. Finally, every pair
of partial survivors is tested on every applicable window with both rows
fixed. This is exhaustive within the stated two-row certificate family and
input domains. No intermediate row is assumed unchanged: trajectories use
the complete edited candidate table throughout.

If a candidate were accepted with a sound old-machine invariant, the local
comparisons and the exact one-step comparisons at all other states would
prove halting equivalence. Both block lengths are positive, and no block
has an intermediate halt. Induction therefore preserves finite halting and
infinite execution. No such candidate was found.

## Results

The baseline is the exact combined238 inherited-label table, SHA-256
069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c.
There are 193 eligible eliminated states and 237 possible retained states
for each, giving 45,741 ordered pairs. Eleven eligible deletions use shift
+2 and 182 use shift -2.

1. Starting at state 95 with every binary radius-five window, compute the
   ordinary abstract transition closure, nondeterministically exposing each
   boundary bit. This is an inductive invariant for every initial tape.
   The screen tested 79,761,416 retained-row actions and found no candidate.
2. Separately collect finite exact execution windows from all 8,386 guarded
   source cases, eight register/spare/gap scenarios each, plus the complete
   409,835-step blank prefix. All 67,088 instruction cases completed: nonhalting instructions reached
   their exact expected whole-tape endpoint, and halting instructions reached
   the designated halt state. The collection has 28,339 windows
   over 36,712,361 literal transitions including the prefix. This smaller
   domain is discovery evidence, not an invariant or an unbounded proof.
   The screen tested 81,391,240 retained-row actions and found no candidate.
3. A supplied three-working-state positive control has two expected
   solutions: delete 10 into 11 with shift +2, or delete 11 into 10 with
   shift -2. The checker finds both.

A rejection can be caused by the finite window or block bounds rather than
semantic inequivalence. Extra helper modifications, nonconstant head
representations, tape transformations, longer blocks and other architectures
are outside this result. The negative result has no bearing on whether a
237-state machine exists.

## Reproduction

Requires Python 3 and a C++17 compiler. Run from this directory:

    g++ -O3 -std=c++17 displaced_fold.cpp -o /tmp/displaced_fold5
    /tmp/displaced_fold5 base238_old.tm
    g++ -O3 -std=c++17 frame_domains238.cpp -o /tmp/frame_domains238
    /tmp/frame_domains238 base238_old.tm sites.txt /tmp/domains5.txt 5 8
    SYNTH_DOMAINS=/tmp/domains5.txt /tmp/displaced_fold5 base238_old.tm
    /tmp/displaced_fold5 positive_control.tm

The expected frame-generator count is exactly 67,088 cases. A malformed
source-site row is an error. The source text uses argument 0 for CH, whose
argument is ignored. `displaced_quotient_receipt.json` records hashes,
parameters and the eligible deleted states. The text logs contain timings,
which are environment dependent.

`displaced_fold.cpp` is a new implementation of this representation and
search. The finite frame collector is adapted from the supplied companion
archive's `research/search/frame_domains.cpp`, changing the bootstrap count
to 409,835 and adding a malformed-input check. It retains that source's
physical-register permutation and frame semantics. The baseline table,
source sites and four-state block semantics remain attributed to the
ProveIt/Wade sources identified in the main 238-state package. No upstream
repository file was modified.
