# Zero first block through the continue-two controller

`PA194ZeroFirstContinue.zeroToContinueTarget` handles the separate case in
which the dense-7 increment-return configuration has first physical block
zero. For any candidate PRA model and model-valued controller and file data,
it follows the zero block to dense 15, then to dense 17, dense 24, and through
the checked 32-step continue-two controller path. Its clock and packed tape
halves are explicit; the remaining file must have an even code `r+r`.
Nonstandard model values and clocks are included.

This is a conditional physical-machine contract. It does not itself supply a
run to the increment-return configuration, establish blank-tape reachability,
identify a source frame or instruction, or prove an iPRA consistency
implication. In particular, the connection to the concrete increment output
and genuine marker-entry theorem is separate from this theorem.

The three modules passed an author suffix rebuild against previously checked
prerequisite overlays, with `propext`, `Classical.choice`, and `Quot.sound`
as their reported axioms and no `sorryAx`. The full nested checker
`check-zero-first-continue.sh` is supplied but has not been run.

An independent ordered suffix replay rebuilt all three zero-first continuation
modules against separately checked controller prerequisites and retained deeper
overlays. It passed without `sorryAx`; this was not a full nested replay.
