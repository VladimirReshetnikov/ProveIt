import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicOrderZero
import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicFixedCutoff
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerFixedCutoffApproximation
import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerIntegralGammaIdentification
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaHalfPlaneInputContinuity

/-!
# The order-zero logarithmic integral is the original Gamma name

Use one common late interval to compare the original ordinary and
logarithmic quadratures. Its geometry comes from the doubled lower
margin. Certificate overlap then returns the original Gamma name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicZeroIdentification

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (source)
open GaussianEulerLogarithmicCommonCutoff (cutoff cutoff_later)
open GaussianEulerLogarithmicCutoffSplit (fullData)
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at denominator_positive)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "I₀" => GaussianEulerLogarithmicImproperName.data zero
local notation "U" => GaussianEulerImproperName.nameF
local notation "UData" => GaussianEulerImproperName.data

private theorem weaker_margin (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) :
    Γ ⊢[PRAAx] source z R B (two*A) := by
  have old := zle_toZ h.andE₁.andE₂.andE₂
  have real : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower z (two*A) B := by
    apply zle_of_toZ (B+two*PolynomialBisection.slack (ZT.ofNat B) (ZT.ofNat A*ComplexLogarithmRemainder.re z))
    simp only [ZT.toZ_ofNat,ZT.toZ_mul] at old ⊢
    dsimp only [PolynomialBisection.slack]
    ipra_simps
    linear_combination 2*old
  exact .andI (.andI (positive_product _ _ (le_of_eq_add (d := one) (by ipra_ring)) h.andE₁.andE₁)
    (.andI h.andE₁.andE₂.andE₁ real)) h.andE₂

theorem cutoff_order_zero (z R B A k : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEulerLogarithmicIntervalName.nameF GaussianGammaEulerCompactQuadrature.nameF
      (fullData zero z R B A k) (GaussianGammaEulerCompactQuadrature.data z R B k (two*A)) := by
  let E := etaDen k (two*A) R
  let T := top k (two*A) R
  let W := width k (two*A) R
  have base := GaussianGammaEulerCompactQuadrature.original_input z R B k (two*A) h.andE₁.andE₂.andE₁
  have interval : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource z R B one W E T :=
    .andI base.andE₁ (.andI (le_refl one) base.andE₂)
  have same := GaussianEulerLogarithmicOrderZero.compact_order_zero z R B one W E T interval
  have degree : Γ ⊢[PRAAx] R+zero ≐ R := add_zero R
  have coefficient : Γ ⊢[PRAAx] GaussianGammaIntegralCutoffs.tailCoefficient (R+zero) ≐ GaussianGammaIntegralCutoffs.tailCoefficient R :=
    congrMul (congrAp2 powF (congrSucc degree) (.eqRefl two)) (congrAp2 factF degree (.eqRefl zero))
  have heightEq : Γ ⊢[PRAAx] height k (two*A) (R+zero) ≐ height k (two*A) R :=
    congrAdd (congrAdd (.eqRefl (k+two*A)) coefficient) (.eqRefl (num 10))
  have etaEq : Γ ⊢[PRAAx] etaDen k (two*A) (R+zero) ≐ E :=
    congrAp2 powF (congrMul (.eqRefl (two*A)) heightEq) (.eqRefl two)
  have topEq : Γ ⊢[PRAAx] top k (two*A) (R+zero) ≐ T := congrMul (.eqRefl two) heightEq
  have widthEq : Γ ⊢[PRAAx] width k (two*A) (R+zero) ≐ W := congrMonus (congrMul etaEq topEq) (.eqRefl one)
  have eq : Γ ⊢[PRAAx] fullData zero z R B A k ≐ GaussianEulerLogarithmicIntervalName.data zero z R B one W E T :=
    GaussianEulerLogarithmicCutoffSplit.interval_data_congr zero z R B one _ _ _ one W E T (.eqRefl one) widthEq etaEq topEq
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ eq.eqSymm (.eqRefl _) same

private theorem matched_diagonal (t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 I t (I₀ z R B A)) (ap2 U t (UData z R B (two*A))) (num 9) (unit t) := by
  let k := cutoff t zero A
  let V := unit t
  let K := unit (t+num 6)
  let H := unit (height k (two*A) R)
  let S := GaussianEulerCutoffCauchyComparison.combined (two*A) R
  have hV := unit_positive (Γ := Γ) t
  have hK := unit_positive (Γ := Γ) (t+num 6)
  have hH := unit_positive (Γ := Γ) (height k (two*A) R)
  have vK : Γ ⊢[PRAAx] le V K := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have pay : Γ ⊢[PRAAx] le (S*V) H := le_trans
    (mul_le_mul_right S (GaussianExponentialReference.unit_monotone (le_trans (cutoff_later t zero A) (le_add_right k (num 6))))
      |> le_congr (by ipra_ring) (by dsimp only [S,GaussianEulerCutoffCauchyComparison.combined]; ipra_ring))
    (le_of_lt (GaussianGammaIntegralCutoffs.omitted_tail_budget k (two*A) R))
  have first := rate_at _ _ _ _ _ _ t t
    (GaussianEulerLogarithmicFixedCutoff.original_fixed_cutoff_rate t zero z R B A k h.andE₁ (le_refl _))
  have logError := distance_radius_mono _ _ _ _ (num 4) V (denominator_positive K t t hK) hV
    (by dsimp only [rateNumerator,rateDenominator,V,K]; ipra_le (2*𝔞(unit t)*𝔞(unit t))*sl vK) first
  have center := cross_at _ _ _ _ t t (cutoff_order_zero z R B A k h)
  have same := distance_radius_mono _ _ _ _ two V (positive_product _ _ hV hV) hV
    (le_congr (.eqRefl _) (by dsimp only [V]; ipra_ring) (le_refl _)) center
  have oldSource := GaussianEulerIntegralGammaIdentification.improper_source z R B (two*A) (weaker_margin z R B A h)
  have last := rate_at _ _ _ _ _ _ t t
    (GaussianEulerFixedCutoffApproximation.original_fixed_cutoff_rate z R B (two*A) k oldSource)
  have plainError := distance_radius_mono _ _ _ _ (num 3) V (denominator_positive H t t hH) hV
    (by dsimp only [rateNumerator,rateDenominator,V,H,S]; ipra_le (𝔞(unit t)*𝔞(unit t))*sl pay) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hV logError
      (distance_triangle_same _ _ _ _ _ _ hV same (distance_symmetric _ _ _ _ hV plainError)))

theorem original_logarithmic_order_zero_is_Gamma (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent I gammaF (I₀ z R B A) (gammaData z R B A) := by
  have doubled := weaker_margin z R B A h
  have oldSource := GaussianEulerIntegralGammaIdentification.improper_source z R B (two*A) doubled
  have integrals : Γ ⊢[PRAAx] crossEquivalent I U (I₀ z R B A) (UData z R B (two*A)) := by
    apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 9)
      (GaussianEulerLogarithmicImproperName.name_regular zero z R B A h.andE₁)
      (GaussianEulerImproperName.name_regular z R B (two*A) oldSource)
    refine .allI ?_
    let sh := fun t : PTm n => Syn.shift t
    have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) :=
      by simpa [Fm.shift,Syn.shift,sh] using h.shift
    simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,sh] using matched_diagonal (var 0) (sh z) (sh R) (sh B) (sh A) hs
  have old := GaussianEulerIntegralGammaIdentification.original_Euler_integral_is_Gamma z R B (two*A) doubled
  have same := GaussianGammaRadiusOverlap.original_Gamma_overlap z R R B one (two*A) one A
    (GaussianGammaHalfPlaneInputContinuity.reciprocal_source z R B (two*A) doubled)
    (GaussianGammaHalfPlaneInputContinuity.reciprocal_source z R B A h)
  exact cross_trans _ _ _ _ _ _ integrals (cross_trans _ _ _ _ _ _ old same)

theorem actual_original_logarithmic_order_zero_is_Gamma_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent I gammaF
      (I₀ (var 0) (var 1) (var 2) (var 3)) (gammaData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_logarithmic_order_zero_is_Gamma _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicZeroIdentification
