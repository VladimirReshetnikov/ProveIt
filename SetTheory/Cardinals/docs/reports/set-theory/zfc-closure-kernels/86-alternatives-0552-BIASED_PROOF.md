# Biased references and a 19-state copying component

Store a reference r as the field 1^(r+3), instead of 1^(r+1). Keep tag fields unchanged. This changes only the encoding of references: the copier returns the original unbiased counter 1^(r+1), so the indexed locator's counter semantics need not change.

## The 21-state construction

Restore the source's first one, erase the following two ones, and inspect the next cell. At loop stage j, for 0 <= j <= r:

- the counter is 1^(j+1);
- the source has a two-zero marker at s+j+1 and s+j+2;
- every other source and arena cell is unchanged;
- the remaining counter gap has length g-j >= 2, assuming g >= r+2.

For j<r the next source cell is one. Shift the two-zero marker right by one, append one counter one, and repeat. For j=r the next cell is the original separator. Restore the two marked ones and return to the counter. Thus the same loop handles r=0 and r=1, removing all special small-value paths and the initial two-unit copying shuttle from the 30-state copier. The termination and whole-tape arguments are those of PROOF.md with this shifted invariant.

## Two exact forced-symbol identifications

In every valid execution of the 21-state construction:

- erase_first is entered only on one; return_left only on zero;
- erase_second is entered only on one; add_loop only on zero.

For the first pair, retain return_left's zero transition and erase_first's one transition. Do the analogous replacement for the second pair. Retarget every incoming transition through the two identifications. No other action changes.

The projection of the old control state, together with the identical tape and head, is a step-by-step simulation. Its induction uses the four forced-read properties above, established by the marker and gap invariants. Consequently termination, output, and every intermediate tape/head coordinate are preserved. The total table has 19 working states, of which 18 are operational and one is a totalizing invariant-failure sink. It has a separate return label. Invalid inputs are outside this component theorem; an eventual fair proof enumerator must never mistake its sink for ordinary certificate rejection.

This is a genuine 11-state component reduction from the original 30-state copier. It is not an 11-state reduction of the existing 246-state consistency machine, which uses a different representation and runtime.

## Variable-length anchor

The single anchor one may be replaced by any positive finite run of ones. Change the after_anchor state's one transition to write one, move right, and remain in after_anchor. The leftward shuttles already traverse arbitrary one-runs, so their proof is unchanged. The rightward shuttle traverses the extra anchor ones and stops at its following zero before entering the field stream.

This permits an anchor run of length 1..4 to retain a two-bit control mode without adding copier states. Fetching, setting, and using that mode elsewhere still require explicitly charged transitions and proof.

## Evidence

- Biased 21-state table: 1,625 whole-tape tests.
- Forced-symbol 19-state table: 2,125 whole-tape tests.
- Variable-anchor 19-state table: 1,260 whole-tape tests, including anchor lengths 1..7 and minimum capacity.

The universal claims rest on the induction and forced-read simulation, not on those finite tests. No Lean compilation is asserted. The Python generators reject assertion-disabled execution.
