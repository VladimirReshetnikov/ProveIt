import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.GaussianNamedEulerLogarithmicDerivative
import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.GaussianNamedEulerLogarithmicParameterRate
import IPRADerivations.Analysis.Gamma.Names.Derivatives.GaussianNamedGammaIncrementApproximation
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedIncrementDifferenceQuotient
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedReciprocalFrozenRate
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedDifferenceRate
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# Logarithmic Euler differentiation along certified nonzero named increments

The increment is a fixed regular complex name with an explicit finite
apartness witness. Its magnitude certificate bounds every observation.
The frozen increment clock is computed from the apartness witness and
the two original named inputs, independently of the raw denominator
at that clock. Its native derivative estimate is transferred to the
actual quotient by the named reciprocal and the original difference.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicNamedDerivative

open_ipra
open GaussianNamedRightHalfPlane (numerator denominator radius)
open GaussianNamedGammaSmallIncrementInput (sumData)
open GaussianNamedGammaIncrementInput (incrementF incrementData)
open GaussianNameReciprocal (anchor R)
open GaussianNamedInverseRate (independentRate)
open GaussianExponentialSmallPerturbation (smallSamples small_samples_at)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianExponentialReference (unit_monotone)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalMetric (bounded)
open GaussianEuclideanDistanceName (pointCN)
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "Named" => GaussianNamedEulerLogarithmicImproper.nameF
local notation "ndata" => GaussianNamedEulerLogarithmicImproper.data
local notation "baseSource" => GaussianNamedRightHalfPlane.source
local notation "sumF" => GaussianNamedGammaSmallIncrementInput.sumF
local notation "diffF" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data
local notation "nativeD" => GaussianNamedEulerLogarithmicDerivative.quotientData

def incrementModulus (f : PR 2) (p j x A : PTm n) : PTm n :=
  GaussianNamedEulerLogarithmicDerivative.incrementModulus f (succ p) j x A
def source (f K : PR 2) (p j x y A a : PTm n) : Fm PTm n :=
  baseSource f x A ⋏ (GaussianNameReciprocal.input K a y ⋏ smallSamples K y one (incrementModulus f p j x A))

def quotientF (f K : PR 2) : PR 2 :=
  GaussianNamedIncrementDifferenceQuotient.nameF (Named (sumF f K)) (Named f) K
def quotientData (f K : PR 2) (j x y A a : PTm n) : PTm n :=
  GaussianNamedIncrementDifferenceQuotient.data (Named (sumF f K)) (Named f) K
    (ndata j (sumData x y) (two*A)) (ndata j x A) y a

def differenceBound (f K : PR 2) (j x y A : PTm n) : PTm n :=
  GaussianNameBounds.U (diffF (Named (sumF f K)) (Named f))
    (diffData (ndata j (sumData x y) (two*A)) (ndata j x A))
def variationPrecision (p a : PTm n) : PTm n := GaussianFastValueCut.exponent (num 10*R a) (succ p)
def variationDemand (f K : PR 2) (p j x y A a : PTm n) : PTm n :=
  GaussianNamedEulerLogarithmicParameterRate.inputRadius (sumF f K) (variationPrecision p a) j (sumData x y) (two*A)
def freezeDelay (f K : PR 2) (p j x y A a : PTm n) : PTm n :=
  GaussianFastValueCut.exponent
    (two*differenceBound f K j x y A*GaussianNameReciprocal.modulus a+two*variationDemand f K p j x y A a) (succ p)
def freezeIndex (f K : PR 2) (p j x y A a : PTm n) : PTm n := freezeDelay f K p j x y A a+anchor a

ipra_subst incrementModulus
ipra_subst source
ipra_subst quotientData

private theorem modulus_positive (f : PR 2) (p j x A : PTm n) : Γ ⊢[PRAAx] le one (incrementModulus f p j x A) :=
  GaussianEulerLogarithmicContinuity.modulus_positive _ _ _ _

theorem shifted_name_source (f K : PR 2) (p j x y A a : PTm n) (hs : Γ ⊢[PRAAx] source f K p j x y A a) :
    Γ ⊢[PRAAx] baseSource (sumF f K) (sumData x y) (two*A) := by
  apply GaussianNamedGammaSmallIncrementInput.original_source f K x y A
  refine .andI hs.andE₁ (.andI hs.andE₂.andE₁.andE₁ ?_)
  let m := incrementModulus f p j x A
  have wide : Γ ⊢[PRAAx] le (num 4*(two*A)) m :=
    le_trans (le_trans (le_add_left _ _) (le_add_right _ _)) (le_add_right _ _)
  have cap : Γ ⊢[PRAAx] le (num 4*A) m :=
    le_trans (le_of_eq_add (d := num 4*A) (by ipra_ring)) wide
  have out : Γ ⊢[PRAAx] le one (num 4*A) :=
    positive_product _ _ (le_of_eq_add (d := num 3) (by ipra_ring)) hs.andE₁.andE₂.andE₁
  have cert : Γ.map Fm.shift ⊢[PRAAx] smallSamples K (Syn.shift y) one (Syn.shift m) := by
    simpa [Fm.shift,Syn.shift,one,m] using hs.andE₂.andE₂.shift
  have pos : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift m) := by
    simpa [Fm.shift,Syn.shift,one,m] using (modulus_positive (Γ := Γ) f p j x A).shift
  have hout : Γ.map Fm.shift ⊢[PRAAx] le one (num 4*Syn.shift A) := by
    simpa [Fm.shift,Syn.shift,one] using out.shift
  have gle : Γ.map Fm.shift ⊢[PRAAx] le (num 4*Syn.shift A) (Syn.shift m) := by
    simpa [Fm.shift,Syn.shift,one] using cap.shift
  refine .allI ?_
  simpa [smallSamples,Syn.shift] using
    bounded_radius_mono (ap2 K (var 0) (Syn.shift y)) one (Syn.shift m) one (num 4*Syn.shift A) pos hout
      (le_congr (by ipra_ring) (by ipra_ring) gle) (small_samples_at K (Syn.shift y) one (Syn.shift m) (var 0) cert)

theorem native_source (f K : PR 2) (p j x y A a : PTm n) (hs : Γ ⊢[PRAAx] source f K p j x y A a) :
    Γ ⊢[PRAAx] GaussianNamedEulerLogarithmicDerivative.source f (succ p) j x A
      (numerator K (freezeIndex f K p j x y A a) y) (denominator K (freezeIndex f K p j x y A a) y) := by
  let t := freezeDelay f K p j x y A a
  let k := freezeIndex f K p j x y A a
  let m := incrementModulus f p j x A
  have sep := GaussianNamedIncrementDifferenceQuotient.late_native_separated K a y t hs.andE₂.andE₁
  have actual := small_samples_at K y one m k hs.andE₂.andE₂
  have bound := (GaussianFastValueCut.recode_bound_iff (ap2 K k y) one m (modulus_positive f p j x A)).iffMpr actual
  exact .andI hs.andE₁ (.andI sep.andE₁ (.andI sep.andE₂ bound))

theorem quotient_input (f K : PR 2) (p j x y A a : PTm n) (hs : Γ ⊢[PRAAx] source f K p j x y A a) :
    Γ ⊢[PRAAx] GaussianNamedIncrementDifferenceQuotient.input (Named (sumF f K)) (Named f) K
      (ndata j (sumData x y) (two*A)) (ndata j x A) y a :=
  .andI (GaussianNamedEulerLogarithmicImproper.name_regular _ _ _ _ (shifted_name_source f K p j x y A a hs))
    (.andI (GaussianNamedEulerLogarithmicImproper.name_regular _ _ _ _ hs.andE₁) hs.andE₂.andE₁)

theorem quotient_regular (f K : PR 2) (p j x y A a : PTm n) (hs : Γ ⊢[PRAAx] source f K p j x y A a) :
    Γ ⊢[PRAAx] pointCN (quotientF f K) (quotientData f K j x y A a) :=
  GaussianNamedIncrementDifferenceQuotient.name_regular _ _ _ _ _ _ _ (quotient_input f K p j x y A a hs)

private theorem total_budget (p a M m t s k : PTm n)
    (hs : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (num 10*R a) (succ p)) s)
    (ht : Γ ⊢[PRAAx] le (GaussianFastValueCut.exponent (two*M*GaussianNameReciprocal.modulus a+two*m) (succ p)) t)
    (hk : Γ ⊢[PRAAx] le t k) :
    Γ ⊢[PRAAx] le (GaussianNamedMultiplyRate.leadingNumerator (GaussianNameReciprocal.modulus a)
      (unit k) (num 5) (unit s) M (R a)*unit (succ p))
      (GaussianNamedMultiplyRate.leadingDenominator (unit k) (unit s)) := by
  let T := unit (succ p)
  let V := GaussianNameReciprocal.modulus a
  let S := unit s
  let U := unit k
  have cut : Γ ⊢[PRAAx] le ((two*M*V+two*m)*T) U :=
    le_trans (GaussianFastValueCut.query_budget _ _) (unit_monotone (le_trans ht hk))
  have first : Γ ⊢[PRAAx] le (two*M*V*T) U := le_trans
    (mul_le_mul_right T (le_add_right _ _)) cut
  have second : Γ ⊢[PRAAx] le ((num 10*R a)*T) S :=
    le_trans (GaussianFastValueCut.query_budget _ _) (unit_monotone hs)
  apply RationalValueBounds.positive_cancel RationalAlgebra.two_positive
  dsimp only [GaussianNamedMultiplyRate.leadingNumerator,GaussianNamedMultiplyRate.leadingDenominator]
  ipra_le 𝔞 S*sl first+𝔞 U*sl second

private theorem constant_bound (v A : PTm n) (h : Γ ⊢[PRAAx] bounded v A one) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound constantF v A := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift v) (Syn.shift A) one :=
    by simpa [Fm.shift,Syn.shift,one] using h.shift
  refine .allI ?_
  simpa [GaussianNamedMultiplyRate.sampleBound,Syn.shift] using
    bound_congr (constant_at (var 0) (Syn.shift v)).eqSymm (.eqRefl _) (.eqRefl _) hs

private theorem actual_name_bound (F : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN F x) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound F x (GaussianNameBounds.U F x) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN F (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa [GaussianNamedMultiplyRate.sampleBound,Syn.shift] using GaussianNameBounds.sample_bound F (Syn.shift x) (var 0) hs

theorem quotient_comparison (f K : PR 2) (p j x y A a : PTm n) (hs : Γ ⊢[PRAAx] source f K p j x y A a) :
    Γ ⊢[PRAAx] independentRate (quotientF f K)
      (GaussianNamedDifferenceQuotient.nameF (Named (incrementF f)) (Named f)) (quotientData f K j x y A a)
      (nativeD f j x A (numerator K (freezeIndex f K p j x y A a) y) (denominator K (freezeIndex f K p j x y A a) y))
      one (unit (succ p)) := by
  let s := variationPrecision p a
  let t := freezeDelay f K p j x y A a
  let k := freezeIndex f K p j x y A a
  let h := numerator K k y
  let D := denominator K k y
  let m := variationDemand f K p j x y A a
  let M := differenceBound f K j x y A
  let X := ndata j (sumData x y) (two*A)
  let Y := ndata j x A
  let W := ndata j (incrementData x h D) (two*A)
  let N := Named (sumF f K)
  let B := Named f
  let L := Named (incrementF f)
  let V := GaussianNameReciprocal.modulus a
  let T := unit (succ p)
  let U := unit k
  let S := unit s
  let inv := GaussianNamedReciprocalFrozenRate.frozen K y k
  have recip := hs.andE₂.andE₁
  have late : Γ ⊢[PRAAx] le (anchor a) k := le_add_left _ _
  have hU : Γ ⊢[PRAAx] le one U := unit_positive k
  have hS : Γ ⊢[PRAAx] le one S := unit_positive s
  have hT : Γ ⊢[PRAAx] le one T := unit_positive _
  have hM : Γ ⊢[PRAAx] le one m := GaussianEulerLogarithmicContinuity.modulus_positive _ _ _ _
  have h2M := positive_product _ _ (le_succ_self one) hM
  have direct : Γ ⊢[PRAAx] le ((two*M*V+two*m)*T) U :=
    le_trans (GaussianFastValueCut.query_budget _ _) (unit_monotone (le_add_right _ _))
  have lift : Γ ⊢[PRAAx] le (two*m) ((two*m)*T) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*m) hT)
  have grow : Γ ⊢[PRAAx] le (two*m) U := le_trans lift (le_trans (mul_le_mul_right T (le_add_left _ _)) direct)
  have named := shifted_name_source f K p j x y A a hs
  have native := native_source f K p j x y A a hs
  have nativeShift := GaussianNamedGammaIncrementInput.original_source f x A h D
    (GaussianNamedEulerLogarithmicDerivative.increment_source f (succ p) j x A h D native)
  have near := GaussianNamedGammaIncrementApproximation.original_rate f K k x y (.andI hs.andE₁.andE₁ recip.andE₁)
  have near' := GaussianNamedRateRadius.weaken _ _ _ _ one U one (two*m) hU h2M
    (le_congr (by ipra_ring) (by ipra_ring) grow) near
  have actual := GaussianNamedEulerLogarithmicParameterRate.original_parameter_rate (sumF f K) (incrementF f)
    s j (sumData x y) (incrementData x h D) (two*A) (two*A)
    (.andI named (.andI nativeShift (GaussianNamedRateComposition.symmetric _ _ _ _ _ _ h2M near')))
  have rate := GaussianNamedRateComposition.symmetric L N W X (num 5) S hS actual
  have nCN : Γ ⊢[PRAAx] pointCN N X := GaussianNamedEulerLogarithmicImproper.name_regular _ _ _ _ named
  have bCN : Γ ⊢[PRAAx] pointCN B Y := GaussianNamedEulerLogarithmicImproper.name_regular _ _ _ _ hs.andE₁
  have lCN : Γ ⊢[PRAAx] pointCN L W := GaussianNamedEulerLogarithmicImproper.name_regular _ _ _ _ nativeShift
  have diff := GaussianNamedDifferenceRate.same_right_rate N L B X W Y (num 5) S hS nCN lCN bCN rate
  have dCN := GaussianNamedDifference.name_regular N B X Y nCN bCN
  have eCN := GaussianNamedDifference.name_regular L B W Y lCN bCN
  have iCN := GaussianNameReciprocal.name_fast K a y recip.andE₁ recip.andE₂
  have cmp := GaussianNamedMultiplyRate.independent_rate (GaussianNameReciprocal.nameF K) (diffF N B)
    constantF (diffF L B) (GaussianNameReciprocal.nameData a y) (diffData X Y) inv (diffData W Y)
    V U (num 5) S M (R a) hU hS iCN dCN (constant_regular inv) eCN
    (actual_name_bound _ _ dCN) (constant_bound inv (R a) (GaussianNamedReciprocalFrozenRate.frozen_inverse_bound K a y k recip late))
    (GaussianNamedReciprocalFrozenRate.frozen_rate K a y k recip late) diff
  apply GaussianNamedRateRadius.weaken _ _ _ _ _ _ one T (positive_product _ _ hU hS) hT ?_ cmp
  exact le_congr (.eqRefl _) (by dsimp only [GaussianNamedMultiplyRate.leadingDenominator,U,S]; ipra_ring)
    (total_budget p a M m t s k (le_refl s) (le_refl t) (le_add_right _ _))

theorem original_derivative_rate (f K : PR 2) (p j x y A a : PTm n) (hs : Γ ⊢[PRAAx] source f K p j x y A a) :
    Γ ⊢[PRAAx] independentRate (quotientF f K) (Named f) (quotientData f K j x y A a) (ndata (succ j) x A) one (unit p) := by
  let k := freezeIndex f K p j x y A a
  let h := numerator K k y
  let D := denominator K k y
  let T := unit (succ p)
  have hT : Γ ⊢[PRAAx] le one T := unit_positive _
  have native := GaussianNamedEulerLogarithmicDerivative.original_derivative_rate f (succ p) j x A h D
    (native_source f K p j x y A a hs)
  have joined := GaussianNamedRateComposition.same_denominator (quotientF f K) _ _ _ (nativeD f j x A h D) _
    one T one hT (quotient_comparison f K p j x y A a hs) native
  apply GaussianNamedRateRadius.weaken _ _ _ _ _ _ one (unit p) hT (unit_positive p) ?_ joined
  have eq : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p := GaussianRationalHalfAngleRecovery.unit_succ p
  exact le_of_eq_add (d := ConciseIPRA.PTm.zero) ((congrMul (.eqRefl one) eq).eqTrans (by ipra_ring))

theorem actual_original_logarithmic_derivative_along_a_named_increment_closed (f K : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source f K (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        independentRate (quotientF f K) (Named f) (quotientData f K (var 1) (var 2) (var 3) (var 4) (var 5))
          (ndata (succ (var 1)) (var 2) (var 4)) one (unit (var 0))) :=
  closeUniv 6 (.impI (original_derivative_rate f K _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicNamedDerivative
