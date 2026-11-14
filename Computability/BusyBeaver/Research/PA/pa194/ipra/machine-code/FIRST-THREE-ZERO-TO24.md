# First physical value three, selected zero: to dense 24

`PA194FirstThreeZeroTo24.markerFirstThreeZeroTo24` follows the first non-first
marker entry when the first physical value is three and the selected value is
zero. Its delimiter hypothesis supplies an actual nonempty following file;
the proof extracts the odd delimiter from that file, follows the zero branch
of dense 42 to dense 84, and composes the scans through dense 15 to dense 24.
It gives the exact returned left half `h = 2*g+1`, where
`g = zeros(2, zeros(6, u))`, and existential model clock and right half.
The original Lean statement gives the complete initial packed tape and all
hypotheses. The independent theorem `scanExitTo24` supplies the precise final
clock contribution and right half for the final segment.

This is a physical execution in every candidate PRA model, including
nonstandard values and clocks. It concerns only the first non-first marker
position, selected value zero, and the stated intermediate layout. It does not
establish reachability from blank tape, identify a source frame or operation,
prove the remaining marker branches, or prove an iPRA consistency direction.

A fresh author suffix replay of the new module passed against retained
previously checked overlays, with `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The complete nested checker
`check-first-three-zero-to24.sh` is provided but has not been run.
