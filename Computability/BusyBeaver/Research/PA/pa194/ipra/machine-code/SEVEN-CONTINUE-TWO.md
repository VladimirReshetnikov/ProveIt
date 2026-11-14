# Increment return through the continue-two controller

`PA194ContinueTwoHeader.continueHeader` applies the checked 32-step
`10111111` → `10111100` transition to the exact header produced by the
increment controller, for an arbitrary candidate PRA model and model-valued
header suffix. `PA194SevenContinueTwo.sevenToContinueTarget` composes it with
the dense-7 to dense-24 theorem. It gives the exact packed starting and ending
tape halves and a model clock equal to the prior controller clock plus 32.

The starting configuration has the increment-return layout: a positive
first physical block of length `k+1`, followed by an even remaining file.
The conclusions hold for nonstandard as well as standard model values. The
composition is conditional on that physical tape shape and does not itself
establish that it is reached from the blank tape, that the source frame
hypotheses hold, or that a source instruction has been simulated. In
particular, it does not instantiate the earlier full marker-entry theorem or
prove a consistency implication.

The two modules were independently rebuilt in a fresh author suffix overlay
against previously checked controller dependencies; their printed axioms were
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The full
nested checker `check-seven-continue-two.sh` is provided but has not been run.
