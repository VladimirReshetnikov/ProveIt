import IPRADerivations.Analysis.GaussianEulerPowerChartFrozenKernel
import IPRADerivations.Analysis.GaussianEulerPowerScalingCompactRate
import IPRADerivations.Analysis.GaussianEulerPositivePowerChartJacobian
import IPRADerivations.Analysis.GaussianGammaReciprocalInverse

/-!
# The original power-damped integrand at a frozen chart point

Cancel the original time multiplier using exact canonical fractions.
The resulting name is the original scale factor divided by the source
time, multiplied by the rescaled image kernel. Its comparison with a
literal image row has a uniform compact rate, including the exact inverse
scale factor and independently requested observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingFrozenIntegrand

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChart (source)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerPowerScalingKernel (scaleF scaleData scaleExpF scaleExpData transformedF transformedData)
open GaussianEulerPowerChartFrozenKernel (parameter imageData cost)
open GaussianPositiveRationalLogarithm (fraction logF)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => GaussianEulerPositivePowerChart.nameF
local notation "Damped" => GaussianEulerPowerScalingCompactRate.nameF
local notation "DampedData" => GaussianEulerPowerScalingCompactRate.data
local notation "EulerRow" => GaussianEulerExponentialSubstitutionIntegrand.productF

abbrev factorF : PR 2 := multiplyF constantF scaleExpF
def factorData (z B e f d h a b : PTm n) : PTm n :=
  multiplyData constantF scaleExpF (fraction b a) (scaleExpData z B e f d h)
def factorBound (z B e f d h E : PTm n) : PTm n := E*GaussianNameBounds.U scaleExpF (scaleExpData z B e f d h)
abbrev frozenF : PR 2 := multiplyF factorF EulerRow
def frozenData (k z B e f d h Q S E T a b : PTm n) : PTm n :=
  multiplyData factorF EulerRow (factorData z B e f d h a b) (imageData k z B e f d h Q S E T a b)

@[simp] theorem subst_scaleExpData {m : ℕ} (σ : Fin n → PTm m) (z B e f d h : PTm n) :
    Syn.subst σ (scaleExpData z B e f d h) = scaleExpData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ e)
      (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) := by
  simp [scaleExpData,scaleData,GaussianGammaFiniteApproximantName.exponentialInputData,scaled,ComplexLogarithmRemainder.scale]
@[simp] theorem subst_factorData {m : ℕ} (σ : Fin n → PTm m) (z B e f d h a b : PTm n) :
    Syn.subst σ (factorData z B e f d h a b) = factorData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ e)
      (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ a) (Syn.subst σ b) := by simp [factorData]
@[simp] theorem subst_factorBound {m : ℕ} (σ : Fin n → PTm m) (z B e f d h E : PTm n) :
    Syn.subst σ (factorBound z B e f d h E) = factorBound (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ e)
      (Syn.subst σ f) (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ E) := by simp [factorBound]

private theorem reciprocal_time (a b : PTm n) (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] qmul (fraction b a) (fraction a b) ≐ qone := by
  have h := GaussianEulerDampedTimeRate.fraction_product b a a b ht.andE₁ ht.andE₂
  have e := GaussianEulerPositivePowerChartJacobian.fraction_congr (a := b*a) (by ipra_ring : Γ ⊢[PRAAx] b*a ≐ one*(a*b))
    (by ipra_ring : Γ ⊢[PRAAx] a*b ≐ one*(a*b))
  exact h.eqTrans (e.eqTrans ((GaussianEulerPositivePowerChartJacobian.fraction_cancel one one (a*b) (le_refl one)
    (positive_product _ _ ht.andE₁ ht.andE₂)).eqTrans
      ((GaussianEulerDecayFactorBounds.fraction_is_radius_point one one (le_refl one)).eqTrans GaussianDominantPairAlgebra.radius_one)))

private theorem cancel_time (F : PR 2) (a b x : PTm n)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) (hF : Γ ⊢[PRAAx] pointCN F x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF (multiplyF constantF F)) F
      (multiplyData constantF (multiplyF constantF F) (fraction b a) (multiplyData constantF F (fraction a b) x)) x := by
  let u := fraction b a
  let v := fraction a b
  let M := multiplyF constantF constantF
  let Y := multiplyData constantF constantF u v
  have hu := constant_regular (Γ := Γ) u
  have hv := constant_regular (Γ := Γ) v
  have h1 := GaussianNameRingLaws.one_fast (Γ := Γ) x
  have assoc := GaussianNameRingLaws.multiply_associative constantF constantF F u v x hu hv hF
  have inv := GaussianGammaReciprocalInverse.constant_inverse u v x (reciprocal_time a b ht)
  have lift := GaussianGammaAdjacentCutoff.multiply_cross M GaussianNameRingLaws.oneF F F Y x x x
    (multiply_fast _ _ _ _ hu hv) h1 hF hF inv (cross_refl _ _ hF)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ assoc)
    (cross_trans _ _ _ _ _ _ lift (GaussianNameRingLaws.multiply_one_left F x hF))

theorem scale_regular (z B e f d h : PTm n) (hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source d h) :
    Γ ⊢[PRAAx] pointCN scaleExpF (scaleExpData z B e f d h) := by
  have log := GaussianPositiveRationalLogarithm.name_regular d h hs
  have linear := GaussianEulerExponentialSubstitutionNamedKernel.linear_regular logF (scaled z f) (B*e)
    (GaussianPositiveRationalLogarithm.data d h) log
  have neg := GaussianNameRingLaws.negative_fast _ _ linear
  exact GaussianRadiusExponentialName.name_regular scaleF _ _
    (GaussianGammaFiniteApproximantName.exponential_input _ _ neg)

theorem factor_regular (z B e f d h a b : PTm n) (hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source d h) :
    Γ ⊢[PRAAx] pointCN factorF (factorData z B e f d h a b) :=
  multiply_fast _ _ _ _ (constant_regular _) (scale_regular z B e f d h hs)

theorem original_factor_sample_bound (p z B e f d h a b E : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (ht : Γ ⊢[PRAAx] le b (E*a))
    (hc : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source d h) :
    Γ ⊢[PRAAx] bounded (ap2 factorF p (factorData z B e f d h a b)) (factorBound z B e f d h E) one := by
  let c := fraction b a
  let x := scaleExpData z B e f d h
  let k := GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus constantF scaleExpF c x) p
  have pairProduct : Γ ⊢[PRAAx] ap2 factorF p (factorData z B e f d h a b) ≐ qmul c (ap2 scaleExpF k x) :=
    (GaussianNameArithmetic.multiply_at constantF scaleExpF c x p).eqTrans
      ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at k c) (.eqRefl _))).eqTrans
        (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))
  have left := GaussianEulerExponentCompactBounds.fraction_bound b a E ha ht
  have right := GaussianNameBounds.sample_bound scaleExpF x k (scale_regular z B e f d h hc)
  exact GaussianRationalReciprocal.bound_congr pairProduct.eqSymm (.eqRefl _) (by ipra_ring)
    (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) left right)

theorem original_factor_bound (z B e f d h a b E : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (ht : Γ ⊢[PRAAx] le b (E*a))
    (hc : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source d h) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound factorF (factorData z B e f d h a b) (factorBound z B e f d h E) := by
  let sh (t : PTm n) := Syn.shift t
  have pa : Γ.map Fm.shift ⊢[PRAAx] le one (sh a) := by simpa [Fm.shift,Syn.shift,sh,one] using ha.shift
  have pt : Γ.map Fm.shift ⊢[PRAAx] le (sh b) (sh E*sh a) := by simpa [Fm.shift,Syn.shift,sh] using ht.shift
  have pc : Γ.map Fm.shift ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (sh d) (sh h) := by
    simpa [Fm.shift,Syn.shift,sh,GaussianPositiveRationalLogarithm.source,one] using hc.shift
  refine .allI ?_
  simpa only [GaussianNamedMultiplyRate.sampleBound,subst_factorData,subst_factorBound,Syn.shift,sh] using
    original_factor_sample_bound (var 0) (sh z) (sh B) (sh e) (sh f) (sh d) (sh h) (sh a) (sh b) (sh E) pa pt pc

theorem original_unweighted_kernel (z B e f d h Q S E T a b : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] crossEquivalent Damped (multiplyF factorF transformedF)
      (DampedData z B e f d h S a b)
      (multiplyData factorF transformedF (factorData z B e f d h a b) (transformedData z B e f d h a b)) := by
  let x := DampedData z B e f d h S a b
  let y := scaleExpData z B e f d h
  let v := transformedData z B e f d h a b
  let u := fraction b a
  let t := fraction a b
  have ht := hs.andE₂.andE₂.andE₁
  have hb := GaussianEulerDampedNamedIntegrand.name_regular C z B a b _ (GaussianEulerPositivePowerChart.name_regular _ _ _ _ _ _ _ _ _ _ hs)
    (.andI hB ht)
  have hc := constant_regular (Γ := Γ) u
  have hu := scale_regular z B e f d h hs.andE₁.andE₂.andE₁
  have hv : Γ ⊢[PRAAx] pointCN transformedF v := GaussianEulerExponentialSubstitutionNamedKernel.name_regular _ _ _ _
    (GaussianEulerPositivePowerChartLogarithm.logarithm_regular _ _ _ _ _ _ _ _ _ _ hs)
  have factor := GaussianEulerDampedNamedIntegrand.original_power_chart_time_factor z B e f d h Q S E T a b (.andI hB hs)
  have lift := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF (multiplyF constantF Damped) (multiplyF scaleExpF transformedF)
    u u (multiplyData constantF Damped t x) (multiplyData scaleExpF transformedF y v)
    hc hc (multiply_fast _ _ _ _ (constant_regular t) hb) (multiply_fast _ _ _ _ hu hv) (cross_refl _ _ hc) factor
  have assoc := GaussianNameRingLaws.multiply_associative constantF scaleExpF transformedF u y v hc hu hv
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (cancel_time Damped a b x ht hb))
    (cross_trans _ _ _ _ _ _ lift (cross_symm _ _ _ _ assoc))

theorem original_frozen_integrand (k z R B e f d h Q S E T a b : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hp : Γ ⊢[PRAAx] parameter z R B e f) (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) :
    Γ ⊢[PRAAx] independentRate Damped frozenF (DampedData z B e f d h S a b) (frozenData k z B e f d h Q S E T a b)
      (factorBound z B e f d h E*cost R h Q S E T) (unit k) := by
  let x := factorData z B e f d h a b
  let y := transformedData z B e f d h a b
  let v := imageData k z B e f d h Q S E T a b
  let a' := GaussianEulerPositivePowerChartImage.numerator k e f d h Q S E T a b
  let b' := GaussianEulerPositivePowerChartImage.denominator k e f d h Q S E T a b
  let W := scaled z f
  let D := B*e
  let M := factorBound z B e f d h E
  let A := cost R h Q S E T
  have hc := hs.andE₁.andE₂.andE₁
  have hF := factor_regular z B e f d h a b hc
  have hx := original_factor_bound z B e f d h a b E hs.andE₂.andE₂.andE₁.andE₁ hs.andE₂.andE₂.andE₂.andE₁ hc
  have hK : Γ ⊢[PRAAx] pointCN transformedF y := GaussianEulerExponentialSubstitutionNamedKernel.name_regular _ _ _ _
    (GaussianEulerPositivePowerChartLogarithm.logarithm_regular _ _ _ _ _ _ _ _ _ _ hs)
  have ht := (GaussianEulerPositivePowerChartImage.image_domain k e f d h Q S E T a b hs).andE₁
  have hEuler := GaussianEulerIntegrandName.name_regular W D a' b' (.andI hp.andE₁ ht)
  have hI : Γ ⊢[PRAAx] pointCN EulerRow v := multiply_fast _ _ _ _ (constant_regular _) hEuler
  have raw := GaussianNamedMultiplyRate.independent_rate factorF transformedF factorF EulerRow x y x v zero one A (unit k)
    (GaussianNameBounds.U transformedF y) M (le_refl one) (unit_positive k) hF hK hF hI
    (GaussianNameBounds.all_samples_bounded transformedF y hK) hx
    (GaussianNamedDifferenceRate.self_rate factorF x hF)
    (GaussianEulerPowerChartFrozenKernel.original_frozen_image_rate k z R B e f d h Q S E T a b hp hs)
  have aligned : Γ ⊢[PRAAx] independentRate (multiplyF factorF transformedF) frozenF (multiplyData factorF transformedF x y)
      (frozenData k z B e f d h Q S E T a b) (M*A) (unit k) :=
    GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) raw
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ (unit_positive k) aligned
    (original_unweighted_kernel z B e f d h Q S E T a b hB hs) (cross_refl _ _ (multiply_fast _ _ _ _ hF hI))

theorem actual_original_frozen_power_damped_integrand_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
      ((le one (var 3) ⋏ parameter (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
        source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) ⟶
        independentRate Damped frozenF
          (DampedData (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9) (var 12) (var 13))
          (frozenData (var 0) (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13))
          (factorBound (var 1) (var 3) (var 4) (var 5) (var 6) (var 7) (var 10)*
            cost (var 2) (var 7) (var 8) (var 9) (var 10) (var 11)) (unit (var 0))) :=
  closeUniv 14 (.impI (original_frozen_integrand _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingFrozenIntegrand
