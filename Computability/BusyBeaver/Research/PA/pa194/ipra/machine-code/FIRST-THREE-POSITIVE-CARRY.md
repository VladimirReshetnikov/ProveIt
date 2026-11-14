# First-three positive branch: traverse the remaining file

`PA194CarryThreeFile.carryThreeAcross` is a model-uniform physical carry
invariant. Starting in dense state 3 on an encoded positive unary block
followed by `n` encoded file blocks, it traverses that block and all `n`
following blocks. If the final file tail is `p+p`, it returns to dense 3
with right half `p`. The final left half and clock are existentially
quantified. The block count `n` is a fixed Lean natural number; the block
contents, suffix, and clock are arbitrary elements of a candidate PRA model,
including nonstandard elements. Its proof inducts only over that fixed
external block count and uses a model-uniform unary scan for each block.

`PA194FirstThreePositiveCarry.markerFirstThreePositiveCarry` composes the
invariant with the genuine first non-first marker path, first physical value
three and positive selected value. Under its stated marker layout and even
final-tail hypothesis, it traverses all encoded remaining blocks in that
layout and reaches dense 3 scanning half the final tail. In particular, a
zero final tail gives a zero right half. This theorem does not establish that
these layout assumptions hold on a reachable machine run or that its endpoint
corresponds to a source-machine frame or operation. Neither consistency
implication follows from this conditional execution.

A fresh author two-module suffix replay passed against retained checked
prerequisite overlays, reporting `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The supplied full nested checker
`check-first-three-positive-carry.sh` has not been run.
An independent ordered suffix replay rebuilt both new modules against
separately checked positive-path and marker/controller objects and retained
deeper overlays. It passed without `sorryAx`; this was not a full nested replay.
