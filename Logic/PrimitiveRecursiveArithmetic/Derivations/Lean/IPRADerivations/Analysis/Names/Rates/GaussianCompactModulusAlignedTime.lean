import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactAlignedTime
import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity

/-!
# A genuine original compact modulus supplies aligned-time observations

The original local rate is used only at zero time distance. The actual
wrapped evaluator queries are read back, preserving their independent
ordinary errors. No output regularity or splitting law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianCompactModulusAlignedTime

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (sampledModulus inside value evaluatorName nameData)
open GaussianCompactAlignedTime (alignedSamples body)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem observations (F : PR 3) (p q a C E L x t u : PTm n)
    (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) (ht : Γ ⊢[PRAAx] inside a C E t) (hu : Γ ⊢[PRAAx] inside a C E u)
    (hd : Γ ⊢[PRAAx] distanceBounded (value t) (value u) zero one) : Γ ⊢[PRAAx]
    distanceBounded (ap3 F p t x) (ap3 F q u x) (unit p+unit q) (unit p*unit q) := by
  have rate := GaussianCompactNamedAdditivity.local_rate F a C E L x t u zero one h (le_refl one) ht hu hd
  have actual := GaussianNamedInverseRate.rate_at (evaluatorName F) (evaluatorName F) (nameData t x) (nameData u x) (L*zero) one p q rate
  exact GaussianRationalDistanceOrder.distance_congr (GaussianCompactRiemannName.evaluator_at F p t x)
    (GaussianCompactRiemannName.evaluator_at F q u x)
    (by unfold GaussianNamedInverseRate.rateNumerator; ipra_ring)
    (by unfold GaussianNamedInverseRate.rateDenominator; ipra_ring) actual

theorem of_sampled_modulus (F : PR 3) (a C E L x : PTm n) (h : Γ ⊢[PRAAx] sampledModulus F a C E L x) : Γ ⊢[PRAAx]
    alignedSamples F a C E x := by
  have hs : (((Γ.map Fm.shift).map Fm.shift).map Fm.shift).map Fm.shift ⊢[PRAAx]
      sampledModulus F (Syn.shift (Syn.shift (Syn.shift (Syn.shift a)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift C))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift E)))) (Syn.shift (Syn.shift (Syn.shift (Syn.shift L))))
        (Syn.shift (Syn.shift (Syn.shift (Syn.shift x)))) := by simpa [Fm.shift,Syn.shift] using h.shift.shift.shift.shift
  refine .allI (.allI (.allI (.allI (.impI (.impI (.impI ?_))))))
  simpa only [body,Syn.shift] using observations F (var 3) (var 2) _ _ _ _ _ (var 1) (var 0) hs.wk.wk.wk
    Prf.hyp1.wk Prf.hyp1 Prf.hyp0

theorem original_compact_modulus_supplies_aligned_time_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sampledModulus F (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ alignedSamples F (var 0) (var 1) (var 2) (var 4)) :=
  closeUniv 5 (.impI (of_sampled_modulus F _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactModulusAlignedTime
