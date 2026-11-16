# First-three positive branch with blank tail: to dense 13

`PA194FirstThreeBlankTailTo13.markerFirstThreeBlankTailTo13` extends the
checked file-return and header path from the genuine first non-first marker
entry, assuming first physical value three, positive selected value `k+1`,
and zero final file tail. The physical execution crosses and returns across
all fixed finitely many following blocks, traverses the remaining unary run,
and reaches dense 13. Both final packed tape halves are specified in Lean:
with `x = (a2+a2+1)+(a2+a2+1)`, the left is `(x+x)+(x+x)` and the right is
`ones(k, returnCode(...))`. The exact input and `a2`/`returnCode` parameters
are in the theorem; the clock is existential.

The finite block count is a standard Lean natural number. The block contents,
`k`, and the clock can be nonstandard model elements. The intermediate marker
layout and blank tail remain hypotheses, and the dense-13 configuration has
not been identified with a source frame. This theorem neither proves
blank-tape reachability nor an iPRA consistency implication.

A fresh author one-module suffix replay passed against retained checked
prerequisite overlays, reporting `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The full nested checker
`check-first-three-blank-tail-to13.sh` is supplied but has not been run.
An independent suffix replay rebuilt this module against separately checked
return and marker/controller objects and retained deeper overlays. It passed
without `sorryAx`; this was not a full nested replay.
