import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerPowerComparison
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerRationalPowerReference

/-!
# The original lower-time Euler power square versus the reciprocal square

The original positive real-part margin implies the actual doubled real
multiplier is at least minus two. Multiplication by the same genuinely
nonpositive harmonic-log observation reverses this order. The resulting
comparison uses the original power square and actual exponential names;
identifying the reciprocal reference is a separate finite code argument.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowTimePowerOrder

open_ipra
open GaussianEulerLowerPowerOrder (source inputF expF leftData radius leftExpData)
open GaussianEulerLowerPowerCoefficients (amplification)
open GaussianEulerUpperPowerCoefficients (realMultiplier)
open GaussianEulerIntegrandName (coefficient powerF)
open GaussianEulerUpperPowerCompatibility (squareF squareData)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (bounded)
open GaussianNamedPositiveExponentialOrder (sampleOrder realOrder)
open ComplexLogarithmRemainder (zeroCode oneCode)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def multiplier : PTm n := realMultiplier zeroCode one
def referenceData (R a b : PTm n) : PTm n := GaussianBoundedConstantProductName.data
  (amplification R) multiplier (GaussianHarmonicLogarithmName.data a b)
def referenceExpData (R a b : PTm n) : PTm n := GaussianRadiusExponentialName.data (radius R b) (referenceData R a b)
ipra_subst multiplier [one]
ipra_subst referenceData
ipra_subst referenceExpData

theorem coefficient_zero_below (A : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (coefficient zeroCode one)) (fstT (coefficient oneCode A)) := by
  let s : ZT n := ComplexLogarithmRemainder.re (GaussianRootAlgebra.sub zeroCode (ComplexLogarithmRemainder.scale one oneCode))
  let t := ComplexLogarithmRemainder.re (GaussianRootAlgebra.sub oneCode (ComplexLogarithmRemainder.scale A oneCode))
  apply RationalArithmetic.order_of_representations _ _ s t one A
    (GaussianEulerIntegrandName.coefficient_represents zeroCode one (le_refl one)).andE₁
    (GaussianEulerIntegrandName.coefficient_represents oneCode A hA).andE₁ (le_refl one) hA
  apply zle_of_toZ one
  simp only [s,t,ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_sub,GaussianRootAlgebra.re_scale,
    GaussianRootAlgebra.re_one,GaussianRootAlgebra.re_zero]
  ipra_simps
  ring

theorem multiplier_below (z R B A : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (multiplier : PTm n)) (fstT (realMultiplier z B)) := by
  have c := RationalArgmin.transitive (coefficient_zero_below A h.andE₁)
    (GaussianEulerLowerPowerCoefficients.coefficient_real_lower z A B h.andE₁ h.andE₂.andE₁.andE₁ h.andE₂.andE₂)
  exact RationalArgmin.rationalLE_congr (GaussianEulerUpperPowerCoefficients.real_multiplier_scalar zeroCode one).eqSymm
    (GaussianEulerUpperPowerCoefficients.real_multiplier_scalar z B).eqSymm
    (GaussianRationalSyntheticBounds.add_monotone _ _ _ _ c c)

theorem multiplier_bound (R : PTm n) : Γ ⊢[PRAAx] bounded (multiplier : PTm n) (amplification R) one := by
  have disk : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source zeroCode one one :=
    .andI (le_refl one) (le_congr ComplexLogarithmRemainder.normSq_zero.eqSymm (by ipra_ring) (zero_le (one : PTm n)))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ one _ one (le_refl one) (le_refl one)
    (le_of_eq_add (d := two*R) (by unfold amplification GaussianEulerUpperPowerCoefficients.amplification; ipra_ring))
    (GaussianEulerUpperPowerCoefficients.real_multiplier_bound zeroCode one one disk)

theorem reference_input (R a b : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b ⋏ le a b) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input inputF (radius R b) (referenceData R a b) :=
  GaussianEulerLowerPowerOrder.product_input _ _ _ _ h (multiplier_bound R)

theorem sample_order_at (p z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (ap2 inputF p (leftData z R B a b))) (fstT (ap2 inputF p (referenceData R a b))) := by
  let s := GaussianBoundedConstantProductName.clock p (amplification R)
  let l := GaussianHarmonicLogarithmName.sample s a b
  have hr := (GaussianHarmonicLogarithmName.sample_real (Γ := Γ) s a b).andE₂
  have order := RationalArithmetic.multiply_antitone (fstT l) (fstT (multiplier : PTm n)) (fstT (realMultiplier z B))
    (GaussianEulerLowerPowerCoefficients.harmonic_sample_nonpositive s a b h.andE₂.andE₂)
    (multiplier_below z R B A h.andE₁)
  have left := (congrFst (GaussianBoundedConstantProductName.sample_at (Γ := Γ) GaussianHarmonicLogarithmName.nameF p
    (amplification R) (realMultiplier z B) (GaussianHarmonicLogarithmName.data a b))).eqTrans
    ((GaussianPositiveExponentialProduct.real_product _ _ hr).eqTrans (RationalAlgebra.multiply_commutative _ _))
  have right := (congrFst (GaussianBoundedConstantProductName.sample_at (Γ := Γ) GaussianHarmonicLogarithmName.nameF p
    (amplification R) (multiplier : PTm n) (GaussianHarmonicLogarithmName.data a b))).eqTrans
    ((GaussianPositiveExponentialProduct.real_product _ _ hr).eqTrans (RationalAlgebra.multiply_commutative _ _))
  exact RationalArgmin.rationalLE_congr left.eqSymm right.eqSymm order

theorem sample_order (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    sampleOrder inputF inputF (leftData z R B a b) (referenceData R a b) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [sampleOrder,Syn.shift,GaussianEulerLowerPowerOrder.subst_leftData,subst_referenceData] using
    sample_order_at (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) hs

theorem ordered_exponentials (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    realOrder expF expF (leftExpData z R B a b) (referenceExpData R a b) :=
  GaussianSignedNameExponentialOrder.original_signed_name_order inputF inputF (radius R b) _ _
    (GaussianEulerLowerPowerOrder.product_input _ _ _ _ h.andE₂
      (GaussianEulerLowerPowerCoefficients.real_multiplier_bound z R B A h.andE₁))
    (reference_input R a b h.andE₂)
    (GaussianEulerUpperPowerOrder.product_real_samples _ _ _ _ (GaussianEulerUpperPowerCoefficients.real_multiplier_axis z B))
    (GaussianEulerUpperPowerOrder.product_real_samples _ _ _ _ (GaussianEulerUpperPowerCoefficients.real_multiplier_axis zeroCode one))
    (sample_order z R B A a b h)

theorem original_square_order (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) : Γ ⊢[PRAAx]
    realOrder squareF expF (squareData z B a b) (referenceExpData R a b) :=
  GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (GaussianEulerLowerPowerComparison.original_power_square z R B A a b h)
    (GaussianNameEquivalence.cross_refl expF (referenceExpData R a b)
      (GaussianRadiusExponentialName.name_regular _ _ _ (reference_input R a b h.andE₂)))
    (ordered_exponentials z R B A a b h)

theorem original_low_time_power_square_reciprocal_reference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      realOrder squareF expF (squareData (var 0) (var 2) (var 4) (var 5)) (referenceExpData (var 1) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_square_order _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLowTimePowerOrder
