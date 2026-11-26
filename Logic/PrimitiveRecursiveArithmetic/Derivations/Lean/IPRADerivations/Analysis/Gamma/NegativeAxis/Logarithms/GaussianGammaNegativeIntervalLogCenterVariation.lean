import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.GaussianGammaNegativeIntervalCenterVariation
import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalLogAbsoluteRetiming
import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.GaussianGammaNegativeIntervalLogChordStationary
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianNamedPositiveLogarithmRate

/-!
# Original negative log-Gamma variation at a small derivative

The uniform positive floor on the signed Gamma magnitude keeps
the logarithm transfer constant independent of the thin chord weight.
The exact original quotient and the strong log chord then retain the
squared separation margin with an explicit derivative residual.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogCenterVariation

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaMinimumSignedStep (centerNumerator centerDenominator)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeIntervalCenterVariation (signed_center_rate)
open GaussianGammaNegativeIntervalChordInverse (poleMargin)
open GaussianGammaNegativeIntervalChordRate (chordWeight cost unit_le_chord_weight)
open GaussianGammaNegativeIntervalGammaSign (signedF signedData)
open GaussianGammaNegativeIntervalLogAbsoluteRetiming (inputF inputData input_cross log_cross margin positive_source)
open GaussianNameEquivalence (cross_symm)
open GaussianNameRingLaws (zeroF)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalHorner (qadd positive_product)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianGammaNegativeIntervalLogAbsolute.nameF
local notation "ld" => GaussianGammaNegativeIntervalLogAbsolute.nameData
local notation "T" => GaussianGammaNegativeIntervalDerivativeTarget.nameF
local notation "td" => GaussianGammaNegativeIntervalDerivativeTarget.data
local notation "R" => GaussianNamedPositiveLogarithm.nameF inputF
local notation "rd" => GaussianGammaNegativeIntervalLogAbsoluteRetiming.nameData

def rateCost (a b N K C : PTm n) : PTm n := margin N*(cost a b N K+C)

theorem original_center_log_rate (p a c b N K C z : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a)
    (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c b K)
    (residual : Γ ⊢[PRAAx] independentRate T zeroF (td a b N) z C (unit p)) : Γ ⊢[PRAAx]
    independentRate L L
      (ld (centerNumerator a c (chordWeight p a b)) (centerDenominator b (chordWeight p a b)) N)
      (ld a b N) (rateCost a b N K C) (chordWeight p a b*unit p) := by
  let W := chordWeight p a b
  let A := centerNumerator a c W
  let D := centerDenominator b W
  let E := W*unit p
  let B := cost a b N K+C
  have hu := unit_positive (Γ := Γ) p
  have hw : Γ ⊢[PRAAx] le one W := le_trans hu (unit_le_chord_weight p a b)
  have he : Γ ⊢[PRAAx] le one E := positive_product _ _ hw hu
  have here := GaussianGammaNegativeIntervalChordStep.center_guard a c b W ha hc hw
  have native := signed_center_rate p a c b N K C z ha hc apart hma hmc residual
  have moved := GaussianNamedRateTransport.transport signedF signedF inputF inputF
    (signedData A D N) (signedData a b N) (inputData A D N) (inputData a b N) B E he native
    (cross_symm _ _ _ _ (input_cross A D N here)) (cross_symm _ _ _ _ (input_cross a b N ha))
  have log := GaussianNamedPositiveLogarithmRate.log_rate inputF inputF
    (inputData A D N) (inputData a b N) (margin N) _ _ B E
    (positive_source A D N here) (positive_source a b N ha) he moved
  exact GaussianNamedRateTransport.transport R R L L (rd A D N) (rd a b N) (ld A D N) (ld a b N)
    (rateCost a b N K C) E he log (log_cross A D N here) (log_cross a b N ha)

theorem stationary_at (p q r a c b N K C z : PTm n)
    (ha : Γ ⊢[PRAAx] guard a b) (hc : Γ ⊢[PRAAx] guard c b) (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a)
    (hma : Γ ⊢[PRAAx] poleMargin a b K) (hmc : Γ ⊢[PRAAx] poleMargin c b K)
    (residual : Γ ⊢[PRAAx] independentRate T zeroF (td a b N) z C (unit r)) : Γ ⊢[PRAAx]
    upper (fstT (qadd (GaussianGammaNegativeIntervalLogThinChord.margin a c b) (ap2 L p (ld a b N))))
      (fstT (ap2 L q (ld c b N))) (rateNumerator (rateCost a b N K C) (unit r) p q) (rateDenominator (unit r) p q) :=
  GaussianGammaNegativeIntervalLogChordStationary.stationary_at p q a c b N (chordWeight r a b)
    (rateCost a b N K C) (unit r) ha hc (GaussianGammaMinimumSignedStep.weight_lower r (b+a) b two)
    (unit_positive r) (original_center_log_rate r a c b N K C z ha hc apart hma hmc residual)

theorem actual_original_negative_interval_stationary_at_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      ((guard (var 3) (var 5) ⋏ (guard (var 4) (var 5) ⋏ ((lt (var 3) (var 4) ⋎ lt (var 4) (var 3)) ⋏
         (poleMargin (var 3) (var 5) (var 7) ⋏ poleMargin (var 4) (var 5) (var 7))))) ⟶
       independentRate T zeroF (td (var 3) (var 5) (var 6)) (var 9) (var 8) (unit (var 2)) ⟶
       upper (fstT (qadd (GaussianGammaNegativeIntervalLogThinChord.margin (var 3) (var 4) (var 5))
          (ap2 L (var 0) (ld (var 3) (var 5) (var 6))))) (fstT (ap2 L (var 1) (ld (var 4) (var 5) (var 6))))
         (rateNumerator (rateCost (var 3) (var 5) (var 6) (var 7) (var 8)) (unit (var 2)) (var 0) (var 1))
         (rateDenominator (unit (var 2)) (var 0) (var 1))) :=
  closeUniv 10 (.impI (.impI (stationary_at _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalLogCenterVariation
