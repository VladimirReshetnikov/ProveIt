import ZFCinPA.SizedStepConn
import ZFCinPA.SizedStepNeg
import ZFCinPA.SizedStepAtom
import ZFCinPA.SizedStepQuant

/-!
# Bounded driver steps

Facade over the bounded step modules of the `hSchema` driver. Every step is
stated at a placeholder level `u`: if the step's placeholder tuple is at level
`u` and the input invariants are derived within `w ≥ wD u`, the output
invariant is derived within `w + 30`.

* `SizedDriverComb`: bounded combinators and `dall2_iff`.
* `SizedDriverLevels`: `tD`, `cD`, `wD`, `invT_le`.
* `SizedStepConn`, `SizedStepNeg`, `SizedStepAtom`, `SizedStepQuant`: the steps.
-/
