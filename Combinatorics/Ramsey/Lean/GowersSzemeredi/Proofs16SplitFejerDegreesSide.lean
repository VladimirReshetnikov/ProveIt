import GowersSzemeredi.Proofs16SplitFejerDegrees
import GowersSzemeredi.Proofs16SplitStepBoundsSide

/-! Declarations of `Proofs16SplitFejerDegrees` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

theorem splitStepDWith_stepP (k a D : Nat) :
    splitStepDWith (stepP k) (stepT k) k a D = splitStepD k a D := by
  unfold splitStepDWith wCountW wExpW wThrDeg wZW wLW wBqW wErW wEbW wPbW wSW wStepY
    splitStepD sCountW sExpW stepThrDeg sZW sLW sBqW sErW sEbW sPbW sSW sQrW sStepY
  rfl

end LeanProofs.GowersSzemeredi
