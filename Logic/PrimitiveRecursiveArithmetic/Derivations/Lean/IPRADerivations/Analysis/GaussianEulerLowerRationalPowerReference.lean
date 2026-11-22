import IPRADerivations.Analysis.GaussianEulerLowerPowerComparison
import IPRADerivations.Analysis.GaussianEulerLowerPowerRebasing
import IPRADerivations.Analysis.GaussianHarmonicLogarithmPower

/-!
# The lower-time reference at t=(a/b)^A is an actual rational power

The original harmonic power name is compared at its actual supplied
clock with the existing scaled logarithm name. Exact multiplier rebasing
and exact reciprocal harmonic observations reduce the reference to the
original integer logarithm product at b/a. Only its genuine independent
query errors remain in the diagonal envelope. Original exponential
properness and the checked integer exponential identify its rational
value, without a supplied logarithm power or output identity.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerRationalPowerReference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLowerPowerCoefficients (lowerMultiplier amplification)
open GaussianEulerLowerPowerRebasing (exponent)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (qnegative distanceBounded)
open GaussianRationalNaturalScale (naturalPoint natScale)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev H : PR 2 := GaussianHarmonicLogarithmName.nameF
abbrev referenceF : PR 2 := GaussianEulerLowerPowerOrder.inputF
abbrev targetF : PR 2 := GaussianHarmonicIntegerExponential.originalExponentF
def source (A a b : PTm n) : Fm PTm n := le one A ⋏ (GaussianPositiveRationalLogarithm.source a b ⋏ le a b)
def referenceData (R A a b : PTm n) : PTm n := GaussianEulerLowerPowerOrder.rightData R A (pw a A) (pw b A)
def targetData (A a b : PTm n) : PTm n := GaussianHarmonicIntegerExponential.originalExponentData (exponent A) b a
def cost (R A : PTm n) : PTm n := two*(amplification R+exponent A)
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (A a b : PTm n) :
    (source A a b).subst σ = source (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [source]
@[simp] theorem subst_referenceData {m : ℕ} (σ : Fin n → PTm m) (R A a b : PTm n) :
    Syn.subst σ (referenceData R A a b) = referenceData (Syn.subst σ R) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [referenceData]
@[simp] theorem subst_targetData {m : ℕ} (σ : Fin n → PTm m) (A a b : PTm n) :
    Syn.subst σ (targetData A a b) = targetData (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [targetData,GaussianHarmonicIntegerExponential.originalExponentData]
@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (R A : PTm n) :
    Syn.subst σ (cost R A) = cost (Syn.subst σ R) (Syn.subst σ A) := by simp [cost]

theorem powered_time_source (A a b : PTm n) (h : Γ ⊢[PRAAx] source A a b) : Γ ⊢[PRAAx]
    GaussianPositiveRationalLogarithm.source (pw a A) (pw b A) ⋏ le (pw a A) (pw b A) :=
  .andI (GaussianHarmonicLogarithmPower.power_source a b A h.andE₂.andE₁) (pw_le_pw A h.andE₂.andE₂)

theorem reciprocal_source (A a b : PTm n) (h : Γ ⊢[PRAAx] source A a b) : Γ ⊢[PRAAx]
    GaussianHarmonicIntegerExponential.source b a a b :=
  .andI h.andE₂.andE₁.andE₁ (GaussianHarmonicLogarithmPower.compact_domain b a (.andI h.andE₂.andE₁.andE₂ h.andE₂.andE₁.andE₁))

theorem target_regular (A a b : PTm n) (h : Γ ⊢[PRAAx] source A a b) : Γ ⊢[PRAAx] pointCN targetF (targetData A a b) :=
  GaussianHarmonicIntegerExponential.original_exponent_regular (exponent A) b a a b (reciprocal_source A a b h)

theorem reference_input (R A a b : PTm n) (h : Γ ⊢[PRAAx] source A a b) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input referenceF (GaussianEulerLowerPowerOrder.radius R (pw b A)) (referenceData R A a b) :=
  GaussianEulerLowerPowerOrder.product_input _ _ _ _ (powered_time_source A a b h)
    (GaussianEulerLowerPowerCoefficients.lower_multiplier_bound R A h.andE₁)

theorem negative_move (x y : PTm n) : Γ ⊢[PRAAx] qmul (qnegative x) y ≐ qmul x (qnegative y) :=
  (GaussianInverseBinomialRows.negative_product x y).eqSymm.eqTrans
    ((GaussianInverseBinomialRows.negative_congr (GaussianRationalPowerAlgebra.qmul_commutative x y)).eqTrans
      ((GaussianInverseBinomialRows.negative_product y x).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _)))

theorem rebase_sample (s A a b : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    qmul (lowerMultiplier A) (natScale A (GaussianHarmonicLogarithmName.sample s a b)) ≐
      natScale (exponent A) (GaussianHarmonicLogarithmName.sample s b a) := by
  let q := GaussianHarmonicLogarithmName.sample s a b
  have first := (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl (lowerMultiplier A))
    (GaussianRationalNaturalScale.natScale_as_product A q)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative (lowerMultiplier A) (naturalPoint A) q).eqSymm.eqTrans
        (GaussianRationalSyntheticDivision.qmul_congr (GaussianEulerLowerPowerRebasing.multiplier_times_A A hA) (.eqRefl q)))
  exact first.eqTrans ((negative_move _ q).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (GaussianEulerLowerPowerRebasing.reciprocal_sample s a b)).eqTrans
      (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm))

theorem diagonal_error (p R A a b : PTm n) (h : Γ ⊢[PRAAx] source A a b) : Γ ⊢[PRAAx]
    distanceBounded (ap2 referenceF p (referenceData R A a b)) (ap2 targetF p (targetData A a b)) (cost R A) (unit p) := by
  let C := lowerMultiplier A
  let X := GaussianHarmonicLogarithmName.data (pw a A) (pw b A)
  let Y := GaussianHarmonicLogarithmPower.scaledData a b A
  let S := GaussianHarmonicLogarithmPower.scaledF
  let s := GaussianBoundedConstantProductName.clock p (amplification R)
  let u := GaussianNamedNaturalScale.clock p A
  let t := GaussianNaturalScaleProductName.clock GaussianPositiveRationalLogarithm.logF p (exponent A) (GaussianPositiveRationalLogarithm.data b a)
  have hpow := GaussianHarmonicLogarithmPower.power_source a b A h.andE₂.andE₁
  have firstRaw := GaussianEulerUpperPowerCompatibility.later_cross H S X Y p s p (le_add_right _ _) (le_refl p)
    (GaussianHarmonicLogarithmPower.harmonic_logarithm_power a b A h.andE₂.andE₁)
  have first := GaussianNameArithmetic.product_distance C C _ _ zero two (unit p) (GaussianNameBounds.U H X) (amplification R) (unit_positive p)
    (GaussianRationalPowerDifference.distance_refl_zero C _ (unit_positive p)) firstRaw
    (GaussianNameBounds.sample_bound H X s (GaussianHarmonicLogarithmName.name_regular _ _ hpow))
    (GaussianEulerLowerPowerCoefficients.lower_multiplier_bound R A h.andE₁)
  have eLeft := GaussianBoundedConstantProductName.sample_at (Γ := Γ) H p (amplification R) C X
  have eMiddle := (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl C)
    (GaussianNamedNaturalScale.sample_at (Γ := Γ) H p A A (GaussianHarmonicLogarithmName.data a b))).eqTrans
      (rebase_sample u A a b h.andE₁)
  have firstPoint : Γ ⊢[PRAAx] distanceBounded (ap2 referenceF p (referenceData R A a b))
      (natScale (exponent A) (GaussianHarmonicLogarithmName.sample u b a)) (two*amplification R) (unit p) :=
    distance_congr eLeft.eqSymm eMiddle (by ipra_ring) (.eqRefl _) first
  have hsRecip : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source b a := .andI h.andE₂.andE₁.andE₂ h.andE₂.andE₁.andE₁
  have secondRaw := GaussianEulerUpperPowerCompatibility.later_cross H GaussianPositiveRationalLogarithm.logF
    (GaussianHarmonicLogarithmName.data b a) (GaussianPositiveRationalLogarithm.data b a) p u t
    (GaussianNamedNaturalScale.clock_later p A) (GaussianNaturalScaleProductName.clock_later _ _ _ _)
    (GaussianNameEquivalence.cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original b a hsRecip))
  have second := GaussianNamedNaturalScale.scaled_distance (exponent A) _ _ two (unit p) (GaussianPositiveRationalLogarithm.radius b a)
    (unit_positive p) secondRaw (GaussianPositiveRationalLogarithm.sample_bound t b a hsRecip)
  have secondPoint : Γ ⊢[PRAAx] distanceBounded
      (natScale (exponent A) (GaussianHarmonicLogarithmName.sample u b a)) (ap2 targetF p (targetData A a b)) (two*exponent A) (unit p) :=
    distance_congr (.eqRefl _) (GaussianNaturalScaleProductName.product_at GaussianPositiveRationalLogarithm.logF p
      (exponent A) (GaussianPositiveRationalLogarithm.data b a)).eqSymm (by ipra_ring) (.eqRefl _) second
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold cost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) firstPoint secondPoint)

theorem exponent_cross (R A a b : PTm n) (h : Γ ⊢[PRAAx] source A a b) : Γ ⊢[PRAAx]
    crossEquivalent referenceF targetF (referenceData R A a b) (targetData A a b) := by
  apply GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (cost R A)
    (reference_input R A a b h).andE₁ (target_regular A a b h)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift A) (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift] using
    diagonal_error (var 0) (Syn.shift R) (Syn.shift A) (Syn.shift a) (Syn.shift b) hs

theorem exponential_rational_power (R A a b : PTm n) (h : Γ ⊢[PRAAx] source A a b) : Γ ⊢[PRAAx]
    crossEquivalent GaussianEulerLowerPowerOrder.expF GaussianGammaCanonicalExponent.constantF
      (GaussianEulerLowerPowerOrder.rightExpData R A (pw a A) (pw b A)) (GaussianHarmonicIntegerExponential.rationalPower b a (exponent A)) := by
  have target := GaussianGammaFiniteApproximantName.exponential_input targetF (targetData A a b) (target_regular A a b h)
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper referenceF targetF
    (GaussianEulerLowerPowerOrder.radius R (pw b A)) (GaussianHarmonicIntegerExponential.originalRadius (exponent A) b a)
    (referenceData R A a b) (targetData A a b) (reference_input R A a b h) target (exponent_cross R A a b h)
  exact cross_trans _ _ _ _ _ _ proper
    (GaussianHarmonicIntegerExponential.original_integer_exponential (exponent A) b a a b (reciprocal_source A a b h))

theorem actual_lower_transformed_reference_rational_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ crossEquivalent GaussianEulerLowerPowerOrder.expF GaussianGammaCanonicalExponent.constantF
      (GaussianEulerLowerPowerOrder.rightExpData (var 0) (var 1) (pw (var 2) (var 1)) (pw (var 3) (var 1)))
      (GaussianHarmonicIntegerExponential.rationalPower (var 3) (var 2) (exponent (var 1)))) :=
  closeUniv 4 (.impI (exponential_rational_power _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerRationalPowerReference
