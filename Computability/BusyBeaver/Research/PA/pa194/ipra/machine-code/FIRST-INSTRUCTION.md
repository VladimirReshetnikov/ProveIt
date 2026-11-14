# PA194 first seeded source instruction

`PA194FirstInstructionComplete.firstInstruction` is a kernel-checked finite
literal-machine run from the exact PA194 seed frame at source site 25 to the
exact formal frame at source site 27. It takes 462 dense-machine steps, leaves
the entire 35-block seed file unchanged, and retains dense root control 24 and
left tape half 1. Four independently kernel-checked blocks cover 128, 128,
128 and 78 transitions. Their initial and final checkpoints are checked
against the startup seed and `frame (path 27) 0 seedFile`, respectively.

`PA194StartupSourceFrame.firstSeedSourceStep` separately identifies the source
instruction: the decrement of logical register 8 takes its zero branch to
site 27 without changing the logical register mapping. The concrete physical
run and this source step therefore agree for the verified seed. This result
is one fixed execution; it is not a general source-instruction simulation.

`PA194FirstInstructionSentence.nativeIPRA` proves, in
`IPRAStandardTheory.standardTheory` (intuitionistic first-order PRA in the
full primitive-recursive function-code language with defining equations and
quantifier-free induction), the closed equation stating that the literal
machine reaches this exact site-27 frame after 58,616 steps from blank. The
clock and final right-tape value are expressed by linear-size binary terms.
This judgment is an object-theory derivability theorem, not merely truth in
Lean's standard natural numbers.

The five intermediate checkpoint values are untrusted outputs of
`generate-first-instruction.py`; the generator pins the dense table and
parent startup checkpoint source. Lean checks each connecting run using
`PA196.FastRun.checked` and separately checks both endpoints. The supplied
`check-first-instruction.sh` rebuilds these modules and the first-instruction
sentence after the source-frame suffix check. It relies on and pins selected
retained prerequisite objects, but does not independently rebuild or pin the
entire transitive dependency closure. A full independent dependency audit
remains separate from this suffix replay.

Neither this fixed concrete trace nor the earlier startup theorem proves an
arbitrary model-length controller simulation or either direction of
`iPRA ⊢ Con(PA) ↔ ¬Halt(M₁₉₄)`.
