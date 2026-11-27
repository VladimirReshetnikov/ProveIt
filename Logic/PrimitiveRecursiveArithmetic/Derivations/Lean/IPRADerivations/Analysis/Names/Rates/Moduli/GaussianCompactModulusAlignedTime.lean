import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactAlignedTime
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactNamedAdditivity

/-!
# A genuine original compact modulus supplies aligned-time observations

The original local rate is used only at zero time distance. The actual
wrapped evaluator queries are read back, preserving their independent
ordinary errors. No output regularity or splitting law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCompactModulusAlignedTime

open_ipra
open GaussianCompactRiemannName (sampledModulus inside value)
open GaussianCompactAlignedTime (alignedSamples)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem observations (F : PR 3) (p q a C E L x t u : PTm n)
    (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) zero one) : Γ ⊢[PRAAx]
    distanceBounded (ap3 F p t x) (ap3 F q u x) (unit p+unit q) (unit p*unit q) :=
  GaussianCompactAlignedTime.modulus_observations F p q a C E L x t u h ht hu hd

theorem of_sampled_modulus (F : PR 3) (a C E L x : PTm n) (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) : Γ ⊢[PRAAx]
    alignedSamples F a C E x :=
  GaussianCompactAlignedTime.of_sampled_modulus F a C E L x h

theorem original_compact_modulus_supplies_aligned_time_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sampledModulus F (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ alignedSamples F (var 0) (var 1) (var 2) (var 4)) :=
  closeUniv 5 (.impI (of_sampled_modulus F _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactModulusAlignedTime
