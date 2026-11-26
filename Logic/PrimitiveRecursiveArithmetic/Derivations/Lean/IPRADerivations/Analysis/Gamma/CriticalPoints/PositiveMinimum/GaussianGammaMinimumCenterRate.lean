import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumSignedStep
import IPRADerivations.Analysis.Gamma.CriticalPoints.PositiveMinimum.GaussianGammaMinimumQuotientReadback
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianNamedPositiveLogarithmRate

/-!
# Small log-Gamma variation along the thin chord

A small first Euler derivative at the base gives a small original
Gamma difference from the base to the selected chord center.
Transport the estimate through the actual positive-log programs.
The denominator retains the chord weight and the leading error
uses the same fixed lower Gamma margin at both endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaMinimumCenterRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaDigammaNative (derivativeData)
open GaussianGammaMinimumSignedStep
  (centerNumerator centerDenominator increment weight weight_lower domain quotientData
    center_source separated_norm step_size original_chord_quotient_rate)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (cross_symm)
open GaussianNameRingLaws (zeroF zero_fast)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator independent_rate)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaLogarithm
  (gammaData gamma_regular gammaRetimedF gammaRetimedData gamma_retimed_cross gammaLogMargin
    logGammaF logGammaData log_input)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "QF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF

def rateCost (M C : PTm n) : PTm n := gammaLogMargin*(M*(one+C))

@[simp] theorem subst_rateCost {k : ℕ} (σ : Fin n → PTm k) (M C : PTm n) :
    Syn.subst σ (rateCost M C) = rateCost (Syn.subst σ M) (Syn.subst σ C) := by
  simp [rateCost, one]

private theorem compose_at (F G H : PR 2) (x y z C N t : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h1 : Γ ⊢[PRAAx] independentRate F G x y one N)
    (h2 : Γ ⊢[PRAAx] independentRate G H y z C N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F t x) (ap2 H t z)
      (diagonalNumerator (one+C) N (num 4) t) (diagonalDenominator N t) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (positive_product _ _ hN (unit_positive t))
      (diagonal_rate F G x y one N t hN h1) (diagonal_rate G H y z C N t hN h2))

private theorem compose_rate (F G H : PR 2) (x y z C N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hh : Γ ⊢[PRAAx] pointCN H z)
    (h1 : Γ ⊢[PRAAx] independentRate F G x y one N)
    (h2 : Γ ⊢[PRAAx] independentRate G H y z C N) :
    Γ ⊢[PRAAx] independentRate F H x z (one+C) N := by
  apply independent_rate F H x z (one+C) N (num 4) hN hf hh
  let s (w : PTm n) := Syn.shift w
  let Δ := Γ.map Fm.shift
  have hN' : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift
  have h1' : Δ ⊢[PRAAx] independentRate F G (s x) (s y) one (s N) :=
    by simpa [Δ,s,Fm.shift,Syn.shift,one] using h1.shift
  have h2' : Δ ⊢[PRAAx] independentRate G H (s y) (s z) (s C) (s N) :=
    by simpa [Δ,s,Fm.shift,Syn.shift] using h2.shift
  refine .allI ?_
  simpa [diagonalEnvelope,Syn.shift,s,one] using compose_at F G H (s x) (s y) (s z) (s C) (s N) (var 0) hN' h1' h2'

theorem original_center_Gamma_rate (p a c b M C z : PTm n) (h : Γ ⊢[PRAAx] domain a c b M)
    (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a)
    (residual : Γ ⊢[PRAAx] independentRate IF zeroF (derivativeData a b) z C (unit p)) :
    Γ ⊢[PRAAx] independentRate gammaF gammaF
      (gammaData (centerNumerator a c (weight p a b M)) (centerDenominator b (weight p a b M)))
      (gammaData a b) (M*(one+C)) (weight p a b M*unit p) := by
  let W := weight p a b M
  let D := centerDenominator b W
  let A := centerNumerator a c W
  let x := gammaData A D
  let y := gammaData a b
  have hw := le_trans (le_succ_self (Γ := Γ) one) (weight_lower p a b M)
  have hs := center_source a c b W h.andE₂.andE₁ h.andE₁.andE₂ hw
  have qsource : Γ ⊢[PRAAx] GaussianNamedDifferenceQuotient.input gammaF gammaF x y (increment a c) D :=
    .andI (gamma_regular A D hs) (.andI (gamma_regular a b h.andE₁) (.andI hs.andE₂ (separated_norm a c apart)))
  have qr := GaussianNamedDifferenceQuotient.name_regular _ _ _ _ _ _ qsource
  have near := compose_rate QF IF zeroF (quotientData a c b W) (derivativeData a b) z C (unit p)
    (unit_positive p) qr (zero_fast z) (original_chord_quotient_rate p a c b M h apart) residual
  exact GaussianGammaMinimumQuotientReadback.original_endpoint_rate _ _ _ _ _ _ z M W (one+C) (unit p)
    qsource (unit_positive p) hw (step_size a c b M W h hw) near

theorem original_center_log_rate (p a c b M C z : PTm n) (h : Γ ⊢[PRAAx] domain a c b M)
    (apart : Γ ⊢[PRAAx] lt a c ⋎ lt c a)
    (residual : Γ ⊢[PRAAx] independentRate IF zeroF (derivativeData a b) z C (unit p)) :
    Γ ⊢[PRAAx] independentRate logGammaF logGammaF
      (logGammaData (centerNumerator a c (weight p a b M)) (centerDenominator b (weight p a b M)))
      (logGammaData a b) (rateCost M C) (weight p a b M*unit p) := by
  let W := weight p a b M
  let D := centerDenominator b W
  let A := centerNumerator a c W
  let x := gammaData A D
  let y := gammaData a b
  let u := gammaRetimedData A D
  let v := gammaRetimedData a b
  have hw := le_trans (le_succ_self (Γ := Γ) one) (weight_lower p a b M)
  have den := positive_product _ _ hw (unit_positive p)
  have hs := center_source a c b W h.andE₂.andE₁ h.andE₁.andE₂ hw
  have rate := original_center_Gamma_rate p a c b M C z h apart residual
  have moved := GaussianNamedRateTransport.transport gammaF gammaF gammaRetimedF gammaRetimedF x y u v
    (M*(one+C)) (W*unit p) den rate (cross_symm _ _ _ _ (gamma_retimed_cross A D hs))
    (cross_symm _ _ _ _ (gamma_retimed_cross a b h.andE₁))
  exact GaussianNamedPositiveLogarithmRate.log_rate _ _ _ _ _ _ _ _ _ (log_input A D hs)
    (log_input a b h.andE₁) den moved

theorem original_Gamma_thin_chord_log_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((domain (var 1) (var 2) (var 3) (var 4) ⋏
        ((lt (var 1) (var 2) ⋎ lt (var 2) (var 1)) ⋏
          independentRate IF zeroF (derivativeData (var 1) (var 3)) (var 6) (var 5) (unit (var 0)))) ⟶
      independentRate logGammaF logGammaF
        (logGammaData (centerNumerator (var 1) (var 2) (weight (var 0) (var 1) (var 3) (var 4)))
          (centerDenominator (var 3) (weight (var 0) (var 1) (var 3) (var 4))))
        (logGammaData (var 1) (var 3)) (rateCost (var 4) (var 5))
        (weight (var 0) (var 1) (var 3) (var 4)*unit (var 0))) :=
  closeUniv 7 (.impI (original_center_log_rate _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaMinimumCenterRate
