# First physical value four: first non-first marker split

`PA194FirstFourFirstSplit.markerFirstFourSplit` follows the genuine first
non-first marker entry when the first physical value is four, using the actual
selected value and nonempty following file. The short controller reaches
dense 61 and then follows the appropriate ten-step branch: a zero selected
value reaches dense 84, and a successor selected value reaches dense 2. The
Lean theorem specifies the full initial and final packed tapes and clock, and
proves the necessary run shapes from the file rather than assuming an
arbitrary delimiter.

The fixed finite file length is a Lean natural number; the values and clock
may be nonstandard elements of a candidate PRA model. The theorem concerns the
first non-first marker position and the stated intermediate tape layout. The
continuations and the other positions remain separate. It does not prove
blank-tape reachability, a source-frame or instruction correspondence, or an
iPRA consistency implication.

A fresh author three-module suffix replay passed against retained checked
prerequisite overlays, reporting `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The full nested checker
`check-first-four-first-split.sh` is supplied but has not been run.
