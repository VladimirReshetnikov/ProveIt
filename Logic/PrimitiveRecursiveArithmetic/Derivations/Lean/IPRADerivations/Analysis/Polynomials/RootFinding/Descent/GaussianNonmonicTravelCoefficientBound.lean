import IPRADerivations.Analysis.Polynomials.Translation.GaussianTranslationCoefficientBound
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianDescentClock
import IPRADerivations.Analysis.Polynomials.RootFinding.DominantTerms.GaussianDominantAlpha
import IPRADerivations.Core.LinearCombination

/-!
# Original coefficient apartness and the actual balanced starting radius

An original coefficient's positive rational lower bound derives actual
nonconstancy. The computed radius-weighted maximum and actual balanced
radius then give the cleared coefficient/radius inequality needed for
travel. Only actual decoded positive denominators are cancelled. The
selected coefficient norm, residual and radius numerator may be zero.
Every degree, coefficient index, fraction and query is numerical input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNonmonicTravelCoefficientBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate represents positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq squaredTolerance)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalNormClearing (weightedNorm)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslation (translated)
open LeanProofs.IPRA.Analysis.GaussianRationalTranslationStages (stage)
open LeanProofs.IPRA.Analysis.GaussianDescentClock (residualNumerator residualDenominator)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq scale normSq_scale)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def selectedIndex (C N z A B : PTm n) : PTm n := GaussianTranslationCoefficientMaximum.winner C N z A B
def selectedCoefficient (C N z A B : PTm n) : PTm n := evaluate (stage C N z (selectedIndex C N z A B)) z
def selectedNumerator (C N z A B : PTm n) : PTm n := normSq (rawGaussian (selectedCoefficient C N z A B))
def selectedDenominator (C N z A B : PTm n) : PTm n := rawDen (selectedCoefficient C N z A B)
def weight (N : PTm n) : PTm n := N*pw two N
def radiusNumerator (C N z : PTm n) : PTm n := GaussianBalancedRadius.radiusNumerator (translated C N z) N
def radiusDenominator (C N z : PTm n) : PTm n := GaussianBalancedRadius.radiusDenominator (translated C N z) N
def radius (C N z : PTm n) : PTm n := GaussianBalancedRadius.radius (translated C N z) N
def lowerBound (C N k L M : PTm n) : Fm PTm n := rationalLE
  (squaredTolerance L M) (qnormSq (entry C (monus N k)))
def combined (C N z A B L M : PTm n) : Fm PTm n :=
  le (L*L*pw (radiusNumerator C N z*B) (two*selectedIndex C N z A B)*(residualDenominator C z*residualDenominator C z))
    (weight N*weight N*M*M*residualNumerator C z*pw (radiusDenominator C N z*A) (two*selectedIndex C N z A B))

@[simp] theorem subst_selectedIndex {m : ℕ} (σ : Fin n → PTm m) (C N z A B : PTm n) :
    Syn.subst σ (selectedIndex C N z A B) = selectedIndex (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) := by simp [selectedIndex]
@[simp] theorem subst_selectedCoefficient {m : ℕ} (σ : Fin n → PTm m) (C N z A B : PTm n) :
    Syn.subst σ (selectedCoefficient C N z A B) = selectedCoefficient (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) := by simp [selectedCoefficient]
@[simp] theorem subst_selectedNumerator {m : ℕ} (σ : Fin n → PTm m) (C N z A B : PTm n) :
    Syn.subst σ (selectedNumerator C N z A B) = selectedNumerator (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) := by simp [selectedNumerator]
@[simp] theorem subst_selectedDenominator {m : ℕ} (σ : Fin n → PTm m) (C N z A B : PTm n) :
    Syn.subst σ (selectedDenominator C N z A B) = selectedDenominator (Syn.subst σ C) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ A) (Syn.subst σ B) := by simp [selectedDenominator]
@[simp] theorem subst_weight {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    Syn.subst σ (weight N) = weight (Syn.subst σ N) := by simp [weight]
@[simp] theorem subst_radiusNumerator {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (radiusNumerator C N z) = radiusNumerator (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [radiusNumerator]
@[simp] theorem subst_radiusDenominator {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (radiusDenominator C N z) = radiusDenominator (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [radiusDenominator]
@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (C N z : PTm n) :
    Syn.subst σ (radius C N z) = radius (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z) := by simp [radius]
@[simp] theorem subst_lowerBound {m : ℕ} (σ : Fin n → PTm m) (C N k L M : PTm n) :
    (lowerBound C N k L M).subst σ = lowerBound (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ k)
      (Syn.subst σ L) (Syn.subst σ M) := by simp [lowerBound]
@[simp] theorem subst_combined {m : ℕ} (σ : Fin n → PTm m) (C N z A B L M : PTm n) :
    (combined C N z A B L M).subst σ = combined (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ L) (Syn.subst σ M) := by simp [combined]

theorem selected_bounds (C N z A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (selectedIndex C N z A B) ⋏ le (selectedIndex C N z A B) N :=
  GaussianTranslationCoefficientMaximum.winner_bounds C N z A B hN
theorem selected_denominator_positive (C N z A B : PTm n) : Γ ⊢[PRAAx]
    le one (selectedDenominator C N z A B) := raw_den_positive _
theorem radius_denominator_positive (C N z : PTm n) : Γ ⊢[PRAAx]
    le one (radiusDenominator C N z) := GaussianBalancedRadius.denominator_positive _ _

theorem lower_cleared (C N k L M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] lowerBound C N k L M) : Γ ⊢[PRAAx]
    le (L*L*(rawDen (entry C (monus N k))*rawDen (entry C (monus N k))))
      (M*M*normSq (rawGaussian (entry C (monus N k)))) :=
  le_congr (by ipra_ring) (by ipra_ring) (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (GaussianRationalMetric.squared_tolerance_represents L M hM)
    (GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive _) (raw_represents _)) h)

/-- The original positive-degree witness is derived from its positive
fractional lower bound, rather than required as another source premise. -/
theorem original_nonconstant (C N k L M : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkN : Γ ⊢[PRAAx] le k N) (hL : Γ ⊢[PRAAx] le one L) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] lowerBound C N k L M) : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.nonconstant C N := by
  have d := raw_den_positive (Γ := Γ) (entry C (monus N k))
  have pos := positive_product _ _ (positive_product L L hL hL) (positive_product _ _ d d)
  have factor := GaussianDominantScalarOrder.factor_positive_left _ _
    (le_congr (.eqRefl _) (mul_comm (M*M) _)
      (le_trans pos (lower_cleared C N k L M hM h)))
  refine .exI k ?_
  simpa [GaussianBalancedRadiusSyntax.nonconstant,GaussianBalancedRadiusSyntax.numerator,GaussianBalancedRadiusSyntax.coefficient] using
    Prf.andI hk (Prf.andI hkN factor)

theorem translated_input (C N z A B k L M : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianTranslationCoefficientBound.input C N z A B)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hL : Γ ⊢[PRAAx] le one L) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] lowerBound C N k L M) : Γ ⊢[PRAAx]
    GaussianBalancedRadius.inputContract (translated C N z) N :=
  GaussianTranslatedNonconstant.radius_input C N z (Prf.andE₁ hInput) (Prf.andE₁ (Prf.andE₂ hInput))
    (original_nonconstant C N k L M hk hkN hL hM h)

theorem selected_represents (C N z A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    represents (GaussianTranslationCoefficientMaximum.base C N z A B)
      (scale (pw A (selectedIndex C N z A B)) (rawGaussian (selectedCoefficient C N z A B)))
      (selectedDenominator C N z A B*pw B (selectedIndex C N z A B)) :=
  GaussianRationalHorner.represents_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqSymm
    (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
    (GaussianDominantPairAlgebra.radial_represents (selectedCoefficient C N z A B) A B (selectedIndex C N z A B) hB)

theorem selected_norm_represents (C N z A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (qnormSq (GaussianTranslationCoefficientMaximum.base C N z A B))
      (ZT.ofNat (pw A (two*selectedIndex C N z A B)*selectedNumerator C N z A B))
      ((selectedDenominator C N z A B*selectedDenominator C N z A B)*pw B (two*selectedIndex C N z A B)) := by
  have rep := GaussianRationalMetric.qnormSq_represents _ _ _
    (positive_product _ _ (selected_denominator_positive C N z A B)
      (RationalNonnegativePowers.denominator_positive B _ hB)) (selected_represents C N z A B hB)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (h := rep)
  · apply ZT.derive
    have e := natEq (normSq_scale (Γ := Γ) (pw A (selectedIndex C N z A B)) (rawGaussian (selectedCoefficient C N z A B)))
    have p := natEq (GaussianDominantAlpha.power_double (Γ := Γ) A (selectedIndex C N z A B))
    simp only [ZT.toZ_ofNat]
    unfold selectedNumerator
    ipra_simps
    linear_combination e-𝔞(normSq (rawGaussian (selectedCoefficient C N z A B)))*p
  · apply deriveNat
    have p := natEq (GaussianDominantAlpha.power_double (Γ := Γ) B (selectedIndex C N z A B))
    ipra_simps
    rw [p]
    ring

theorem weighted_selected_represents (C N z A B K : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (weightedNorm K (GaussianTranslationCoefficientMaximum.base C N z A B))
      (ZT.ofNat (K*pw A (two*selectedIndex C N z A B)*selectedNumerator C N z A B))
      ((selectedDenominator C N z A B*selectedDenominator C N z A B)*pw B (two*selectedIndex C N z A B)) := by
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _
    (fraction_represents K one (le_refl one)) (selected_norm_represents C N z A B hB)
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) (hAB := one_mul _) (h := rep)
  ipra_lc

theorem selected_lower (C N z A B k L M : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianTranslationCoefficientBound.input C N z A B)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hM : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] lowerBound C N k L M) : Γ ⊢[PRAAx]
    le (L*L*(selectedDenominator C N z A B*selectedDenominator C N z A B)*pw B (two*selectedIndex C N z A B))
      (weight N*weight N*M*M*pw A (two*selectedIndex C N z A B)*selectedNumerator C N z A B) := by
  let q := entry C (monus N k)
  let d := rawDen q
  let e := two*selectedIndex C N z A B
  let f := (selectedDenominator C N z A B*selectedDenominator C N z A B)*pw B e
  have hB := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ hInput))
  have quant := GaussianTranslationCoefficientBound.source_coefficient_bound C N z A B k hInput hk hkN
  have cleared : Γ ⊢[PRAAx] le (f*normSq (rawGaussian q))
      (weight N*weight N*pw A e*selectedNumerator C N z A B*(d*d)) :=
    le_congr (by unfold f; ipra_ring) (by ipra_ring)
      (GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
        (GaussianRationalNormClearing.weighted_norm_represents (one*one) q (rawGaussian q) d
          (raw_den_positive q) (raw_represents q))
        (weighted_selected_represents C N z A B (weight N*weight N) hB) quant)
  have lower := mul_le_mul_right f (lower_cleared C N k L M hM h)
  have upper := mul_le_mul_right (M*M) cleared
  have first : Γ ⊢[PRAAx] le ((d*d)*(L*L*f))
      (f*normSq (rawGaussian q)*(M*M)) := le_congr (by ipra_ring) (by ipra_ring) lower
  have last : Γ ⊢[PRAAx] le (f*normSq (rawGaussian q)*(M*M))
      ((d*d)*(weight N*weight N*M*M*pw A e*selectedNumerator C N z A B)) :=
    le_congr (.eqRefl _) (by ipra_ring) upper
  exact le_congr (by unfold f; ipra_ring) (.eqRefl _)
    (RationalValueBounds.positive_cancel (positive_product d d (raw_den_positive q) (raw_den_positive q)) (le_trans first last))

theorem radius_term_represents (C N z A B : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (GaussianBalancedRadius.term (translated C N z) N (selectedIndex C N z A B))
      (ZT.ofNat (selectedNumerator C N z A B*pw (radiusNumerator C N z) (two*selectedIndex C N z A B)))
      ((selectedDenominator C N z A B*selectedDenominator C N z A B)*
        pw (radiusDenominator C N z) (two*selectedIndex C N z A B)) := by
  have hi := Prf.andE₂ (selected_bounds C N z A B hN)
  have code : Γ ⊢[PRAAx] GaussianBalancedRadius.term (translated C N z) N (selectedIndex C N z A B) ≐
      RationalArithmetic.multiply (qnormSq (selectedCoefficient C N z A B))
        (RationalNonnegativePowers.power (radiusNumerator C N z) (radiusDenominator C N z) (two*selectedIndex C N z A B)) :=
    RationalAlgebra.multiply_congr (GaussianRationalProductWitness.qnormSq_congr
      (GaussianRationalTranslation.ascending_coefficient C N z (selectedIndex C N z A B) hi)) (.eqRefl _)
  have numeratorValue : Γ ⊢[PRAAx] RationalArithmetic.represents (qnormSq (selectedCoefficient C N z A B))
      (ZT.ofNat (selectedNumerator C N z A B)) (selectedDenominator C N z A B*selectedDenominator C N z A B) :=
    GaussianRationalMetric.qnormSq_represents _ _ _ (selected_denominator_positive C N z A B)
      (raw_represents (selectedCoefficient C N z A B))
  have powerValue := RationalNonnegativePowers.power_represents (Γ := Γ) (radiusNumerator C N z) (radiusDenominator C N z)
    (two*selectedIndex C N z A B) (radius_denominator_positive C N z)
  have rep := RationalRepresentations.represents_multiply (Γ := Γ) _ _ _ _ _ _ numeratorValue powerValue
  apply GaussianRationalHorner.scalar_congr code.eqSymm (hAB := .eqRefl _) (h := rep)
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps

theorem selected_radius_cleared (C N z A B k L M : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianTranslationCoefficientBound.input C N z A B)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hL : Γ ⊢[PRAAx] le one L) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] lowerBound C N k L M) : Γ ⊢[PRAAx]
    le (selectedNumerator C N z A B*pw (radiusNumerator C N z) (two*selectedIndex C N z A B)*
        (residualDenominator C z*residualDenominator C z))
      (residualNumerator C z*(selectedDenominator C N z A B*selectedDenominator C N z A B)*
        pw (radiusDenominator C N z) (two*selectedIndex C N z A B)) := by
  have hN := Prf.andE₁ (Prf.andE₂ hInput)
  have bounds := selected_bounds C N z A B hN
  have radiusBound := GaussianBalancedRadius.coefficient_bound (translated C N z) N (selectedIndex C N z A B)
    (translated_input C N z A B k L M hInput hk hkN hL hM h) (Prf.andE₁ bounds) (Prf.andE₂ bounds)
  have valueBound := RationalArgmin.rationalLE_congr (.eqRefl _)
    (GaussianRationalProductWitness.qnormSq_congr (GaussianRationalTranslation.ascending_constant C N z)) radiusBound
  have clear := GaussianRationalMetric.comparison_to_cleared (Γ := Γ) _ _ _ _ _ _ (radius_term_represents C N z A B hN)
    (GaussianRationalMetric.qnormSq_represents _ _ _ (GaussianDescentClock.residual_denominator_positive C z)
      (GaussianDescentClock.value_represents (evaluate C z))) valueBound
  exact le_congr (by ipra_ring) (by unfold GaussianDescentClock.residualNumerator; ipra_ring) clear

/-- No selected coefficient norm is cancelled: its two actual decoded
denominators are positive even when the selected value or residual is zero. -/
theorem coefficient_radius_bound (C N z A B k L M : PTm n)
    (hInput : Γ ⊢[PRAAx] GaussianTranslationCoefficientBound.input C N z A B)
    (hk : Γ ⊢[PRAAx] le one k) (hkN : Γ ⊢[PRAAx] le k N)
    (hL : Γ ⊢[PRAAx] le one L) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] lowerBound C N k L M) : Γ ⊢[PRAAx] combined C N z A B L M := by
  let e := two*selectedIndex C N z A B
  let ds := selectedDenominator C N z A B
  let dn := residualDenominator C z*residualDenominator C z
  let a := radiusNumerator C N z
  let b := radiusDenominator C N z
  have lower := mul_le_mul_right (pw a e*dn) (selected_lower C N z A B k L M hInput hk hkN hM h)
  have upper := mul_le_mul_right (weight N*weight N*M*M*pw A e)
    (selected_radius_cleared C N z A B k L M hInput hk hkN hL hM h)
  have first : Γ ⊢[PRAAx] le ((ds*ds)*(L*L*pw a e*pw B e*dn))
      (selectedNumerator C N z A B*pw a e*dn*(weight N*weight N*M*M*pw A e)) :=
    le_congr (by ipra_ring) (by ipra_ring) lower
  have last : Γ ⊢[PRAAx] le
      (selectedNumerator C N z A B*pw a e*dn*(weight N*weight N*M*M*pw A e))
      ((ds*ds)*(weight N*weight N*M*M*residualNumerator C z*pw b e*pw A e)) :=
    le_congr (.eqRefl _) (by ipra_ring) upper
  have clear := RationalValueBounds.positive_cancel
    (positive_product ds ds (selected_denominator_positive C N z A B) (selected_denominator_positive C N z A B))
    (le_trans first last)
  apply le_congr (h := clear)
  · apply deriveNat
    have p := natEq (GaussianProductStability.power_product (Γ := Γ) a B e)
    unfold dn
    ipra_simps
    rw [p]
    ring
  · apply deriveNat
    have p := natEq (GaussianProductStability.power_product (Γ := Γ) b A e)
    ipra_simps
    rw [p]
    ring

end LeanProofs.IPRA.Analysis.GaussianNonmonicTravelCoefficientBound
