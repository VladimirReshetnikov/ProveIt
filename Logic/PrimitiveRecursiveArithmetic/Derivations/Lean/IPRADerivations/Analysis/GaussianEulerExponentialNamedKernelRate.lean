import IPRADerivations.Analysis.GaussianEulerExponentialSubstitutionNamedKernel
import IPRADerivations.Analysis.GaussianRadiusExponentialLipschitzRate
import IPRADerivations.Analysis.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.GaussianNamedRateTransport
import IPRADerivations.Analysis.GaussianGammaEulerHead

/-!
# Actual exponential substitution kernel on a common input disk

For arbitrary regular complex input names, the original nested program
`exp((z/B)*u-exp(u))` preserves an independent input rate. Both inner and
outer exponential samplers retain their own computed radii and clocks.
The common disks and the gain are derived from the actual input samples.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerExponentialNamedKernelRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerExponentialSubstitutionNamedKernel
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (ofGaussian qadd qmul qzero positive_product)
open GaussianRationalMetric (bounded qsub qnegative distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum bounded_negative)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def innerBound (S : PTm n) : PTm n := pw (num 3) S
def exponentRadius (R S : PTm n) : PTm n := R*S+innerBound S
def gain (R S : PTm n) : PTm n := pw (num 3) (exponentRadius R S)*(R+innerBound S)
def source (f g : PR 2) (z R B S x y A D : PTm n) : Fm PTm n :=
  (le one B ⋏ ComplexLogarithmRemainder.bounded z (R*B)) ⋏
  ((GaussianRadiusExponentialName.input f S x ⋏ GaussianRadiusExponentialName.input g S y) ⋏
    (le one D ⋏ independentRate f g x y A D))

@[simp] theorem subst_innerBound {m : ℕ} (σ : Fin n → PTm m) (S : PTm n) :
    Syn.subst σ (innerBound S) = innerBound (Syn.subst σ S) := by simp [innerBound]
@[simp] theorem subst_exponentRadius {m : ℕ} (σ : Fin n → PTm m) (R S : PTm n) :
    Syn.subst σ (exponentRadius R S) = exponentRadius (Syn.subst σ R) (Syn.subst σ S) := by simp [exponentRadius]
@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R S : PTm n) :
    Syn.subst σ (gain R S) = gain (Syn.subst σ R) (Syn.subst σ S) := by simp [gain]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f g : PR 2) (z R B S x y A D : PTm n) :
    (source f g z R B S x y A D).subst σ = source f g (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ S) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ A) (Syn.subst σ D) := by simp [source]

/-- The actual own-radius exponential, bounded at its actual input query. -/
theorem inner_observation_bound (f : PR 2) (p S x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f S x) : Γ ⊢[PRAAx]
    bounded (ap2 (innerF f) p (innerData f x)) (innerBound S) one := by
  let U := GaussianNameBounds.U f x
  have old := GaussianRadiusExponentialName.bounded_samples_at f S x
    (GaussianRadiusExponentialName.inputPrecision U p) h.andE₂
  exact bound_congr (GaussianRadiusExponentialName.sample_at f U p x).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveExponentialMajorant.disk_bound _ S (GaussianRadiusExponentialName.index U p) old)

theorem linear_observation_bound (f : PR 2) (p z R B S x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f S x) : Γ ⊢[PRAAx]
    bounded (ap2 (linearF f) p (linearData f z B x)) (R*S) one := by
  have old := GaussianRadiusExponentialName.bounded_samples_at f S x
    (GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus constantF f (ofGaussian z B) x) p) h.andE₂
  exact bound_congr (linear_at f p z B x).eqSymm (.eqRefl _) (by ipra_ring)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) (GaussianGammaEulerHead.fraction_disk z R B hB hz) old)

private theorem negative_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianNameRingLaws.negativeF f) p (GaussianNameRingLaws.negativeData x) ≐
      qnegative (ap2 f (GaussianFastValueCut.exponent (one+one) p) x) :=
  (GaussianNameRingLaws.negative_at f x p).eqTrans
    ((GaussianNameArithmetic.recode_congr
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalMetric.qnegative_canonical _)))

theorem exponent_observation_bound (f : PR 2) (p z R B S x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f S x) : Γ ⊢[PRAAx]
    bounded (ap2 (exponentF f) p (exponentData f z B x)) (exponentRadius R S) one := by
  let q := GaussianFastValueCut.exponent two p
  have pos := linear_observation_bound f q z R B S x hB hz h
  have neg := bound_congr (negative_at (innerF f) q (innerData f x)).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_negative _ _ _ (le_refl one)
      (inner_observation_bound f (GaussianFastValueCut.exponent (one+one) q) S x h))
  have eq := (exponent_at (Γ := Γ) f p z B x).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _))
  exact bound_congr eq.eqSymm (by unfold exponentRadius; ipra_ring) (by ipra_ring)
    (bounded_sum _ _ _ _ _ _ (le_refl one) (le_refl one) pos neg)

theorem common_exponent_input (f : PR 2) (z R B S x : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f S x) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input (exponentF f) (exponentRadius R S) (exponentData f z B x) := by
  refine .andI (exponent_regular f z B x h.andE₁) (.allI ?_)
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have zs : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
    simpa [Fm.shift,Syn.shift] using hz.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianRadiusExponentialName.input f (Syn.shift S) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,subst_exponentRadius,subst_exponentData,Syn.shift] using
    exponent_observation_bound f (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift S) (Syn.shift x) bs zs hs

theorem inner_rate (f g : PR 2) (S x y A D : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f S x)
    (hg : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input g S y)
    (hD : Γ ⊢[PRAAx] le one D) (hr : Γ ⊢[PRAAx] independentRate f g x y A D) : Γ ⊢[PRAAx]
    independentRate (innerF f) (innerF g) (innerData f x) (innerData g y) (innerBound S*A) D := by
  have raw := GaussianRadiusExponentialLipschitzRate.independent_rate f g S x y A D (.andI hD (.andI hf (.andI hg hr)))
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hD raw
    (GaussianExponentialRadiusIndependence.same_input_cross f _ S x (GaussianGammaFiniteApproximantName.exponential_input f x hf.andE₁) hf)
    (GaussianExponentialRadiusIndependence.same_input_cross g _ S y (GaussianGammaFiniteApproximantName.exponential_input g y hg.andE₁) hg)

theorem linear_rate (f g : PR 2) (z R B S x y A D : PTm n)
    (h : Γ ⊢[PRAAx] source f g z R B S x y A D) : Γ ⊢[PRAAx]
    independentRate (linearF f) (linearF g) (linearData f z B x) (linearData g z B y) (R*A) D := by
  have hf := h.andE₂.andE₁.andE₁
  have hg := h.andE₂.andE₁.andE₂
  have constantBound : Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound constantF (ofGaussian z B) R := by
    refine .allI ?_
    have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.andE₁.andE₁.shift
    have zs : Γ.map Fm.shift ⊢[PRAAx] ComplexLogarithmRemainder.bounded (Syn.shift z) (Syn.shift R*Syn.shift B) := by
      simpa [Fm.shift,Syn.shift] using h.andE₁.andE₂.shift
    simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianRationalHorner.subst_ofGaussian,Syn.shift] using
      bound_congr (constant_at (var 0) (ofGaussian (Syn.shift z) (Syn.shift B))).eqSymm (.eqRefl _) (.eqRefl _)
        (GaussianGammaEulerHead.fraction_disk (Syn.shift z) (Syn.shift R) (Syn.shift B) bs zs)
  have raw := GaussianNamedMultiplyRate.independent_rate constantF f constantF g
    (ofGaussian z B) x (ofGaussian z B) y zero one A D S R (le_refl one) h.andE₂.andE₂.andE₁
    (constant_regular _) hf.andE₁ (constant_regular _) hg.andE₁ hf.andE₂ constantBound
    (GaussianNamedDifferenceRate.self_rate constantF _ (constant_regular _)) h.andE₂.andE₂.andE₂
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
    (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) raw

private theorem cancel_denominator (F G : PR 2) (x y K D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] independentRate F G x y (K*D) (D*D)) : Γ ⊢[PRAAx] independentRate F G x y K D := by
  let sh := fun t : PTm n => Syn.shift (Syn.shift t)
  have ds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh] using hD.shift.shift
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate F G (sh x) (sh y) (sh K*sh D) (sh D*sh D) := by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift,sh] using GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _
    (rateNumerator (sh K) (sh D) (var 1) (var 0)) (rateDenominator (sh D) (var 1) (var 0))
    (GaussianNamedInverseRate.denominator_positive _ _ _ (positive_product _ _ ds ds))
    (GaussianNamedInverseRate.denominator_positive _ _ _ ds)
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring))
    (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) hs)

theorem exponent_rate (f g : PR 2) (z R B S x y A D : PTm n)
    (h : Γ ⊢[PRAAx] source f g z R B S x y A D) : Γ ⊢[PRAAx]
    independentRate (exponentF f) (exponentF g) (exponentData f z B x) (exponentData g z B y) ((R+innerBound S)*A) D := by
  have hf := h.andE₂.andE₁.andE₁
  have hg := h.andE₂.andE₁.andE₂
  have hd := h.andE₂.andE₂.andE₁
  have raw := GaussianNamedDifferenceRate.original_rate (linearF f) (innerF f) (linearF g) (innerF g)
    (linearData f z B x) (innerData f x) (linearData g z B y) (innerData g y) (R*A) D (innerBound S*A) D
    (.andI (.andI hd hd) (.andI (.andI (linear_regular f z B x hf.andE₁) (inner_regular f x hf.andE₁))
      (.andI (.andI (linear_regular g z B y hg.andE₁) (inner_regular g y hg.andE₁))
        (.andI (linear_rate f g z R B S x y A D h) (inner_rate f g S x y A D hf hg hd h.andE₂.andE₂.andE₂)))))
  have combined : Γ ⊢[PRAAx] independentRate (exponentF f) (exponentF g) (exponentData f z B x) (exponentData g z B y)
      (((R+innerBound S)*A)*D) (D*D) :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by unfold GaussianNamedDifferenceRate.leadingNumerator; ipra_ring) (.eqRefl _) raw
  exact cancel_denominator _ _ _ _ _ _ hd combined

/-- The actual branchless kernel, with its independently computed radii. -/
theorem original_rate (f g : PR 2) (z R B S x y A D : PTm n)
    (h : Γ ⊢[PRAAx] source f g z R B S x y A D) : Γ ⊢[PRAAx]
    independentRate (nameF f) (nameF g) (data f z B x) (data g z B y) (gain R S*A) D := by
  have hf := h.andE₂.andE₁.andE₁
  have hg := h.andE₂.andE₁.andE₂
  have hd := h.andE₂.andE₂.andE₁
  have ef := common_exponent_input f z R B S x h.andE₁.andE₁ h.andE₁.andE₂ hf
  have eg := common_exponent_input g z R B S y h.andE₁.andE₁ h.andE₁.andE₂ hg
  have raw := GaussianRadiusExponentialLipschitzRate.independent_rate (exponentF f) (exponentF g)
    (exponentRadius R S) (exponentData f z B x) (exponentData g z B y) ((R+innerBound S)*A) D
    (.andI hd (.andI ef (.andI eg (exponent_rate f g z R B S x y A D h))))
  have transferred := GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hd raw
    (GaussianExponentialRadiusIndependence.same_input_cross (exponentF f) _ (exponentRadius R S) (exponentData f z B x)
      (original_input f z B x hf.andE₁) ef)
    (GaussianExponentialRadiusIndependence.same_input_cross (exponentF g) _ (exponentRadius R S) (exponentData g z B y)
      (original_input g z B y hg.andE₁) eg)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold GaussianRadiusExponentialLipschitzRate.factor gain; ipra_ring) (.eqRefl _) transferred

theorem original_observations (f g : PR 2) (p q z R B S x y A D : PTm n)
    (h : Γ ⊢[PRAAx] source f g z R B S x y A D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data f z B x)) (ap2 (nameF g) q (data g z B y))
      (rateNumerator (gain R S*A) D p q) (rateDenominator D p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_rate f g z R B S x y A D h)

theorem actual_exponential_substitution_kernel_input_rate_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      independentRate (nameF f) (nameF g) (data f (var 0) (var 2) (var 4)) (data g (var 0) (var 2) (var 5))
        (gain (var 1) (var 3)*var 6) (var 7)) :=
  closeUniv 8 (.impI (original_rate f g _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerExponentialNamedKernelRate
