import IPRADerivations.Analysis.Stirling.Raabe.UnitPanels.GaussianRaabeUnitGridRecurrence

/-!
# The real log-Gamma recurrence on shifted compact quadratures

The original uniform left tags are paired across a shift by one.
Summing the pointwise recurrence retains the exact interval width in
the observation error, including the case of zero width.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeStripGridRecurrence

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianCompactRiemannName (quadrature)
open GaussianRaabeUnitGridRecurrence (logGammaEvaluator logEvaluator strip_quadrature_error)
open GaussianRationalMetric (distanceBounded qsub)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem quadrature_error (p N A C D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded
      (qsub (quadrature logGammaEvaluator p N (A+D) C D zero)
        (quadrature logGammaEvaluator p N A C D zero))
      (quadrature logEvaluator p N A C D zero) (C*num 8) (D*unit p) :=
  strip_quadrature_error p N A C D hN hA hD

theorem actual_shifted_log_Gamma_strip_quadratures_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let p := var 0
       let N := var 1
       let A := var 2
       let C := var 3
       let D := var 4
       (le one N ⋏ (le one A ⋏ le one D)) ⟶
         distanceBounded (qsub (quadrature logGammaEvaluator p N (A+D) C D zero)
           (quadrature logGammaEvaluator p N A C D zero))
           (quadrature logEvaluator p N A C D zero) (C*num 8) (D*unit p)) :=
  closeUniv 5 (.impI (quadrature_error _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeStripGridRecurrence
