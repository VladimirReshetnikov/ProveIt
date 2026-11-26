import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalFactorApartness
import IPRADerivations.Analysis.Names.Rates.GaussianNamedSmallPerturbationTransport
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedSize

/-!
# Deflation of one original Barnes factor

The integer power of the translated argument is factored from the literal
original observation. The remaining multiplier uses the same exponential
program and has its own checked regular name and apartness certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedFactor

open_ipra
open GaussianBarnesCanonicalFactor (source base powerValue exponentialF exponentialData exponentRadius correction)
open GaussianBarnesCanonicalFactorApartness (minimumClock denominator denominator_positive power_lower)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaEulerHeadLower (translated)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (ofGaussian ofGaussian_represents qmul qmul_canonical qmul_represents positive_product canonical_unique
  represents_congr)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalPowerAlgebra (power_product)
open GaussianReciprocalHorner (qmul_associative)
open GaussianRationalReciprocal (power powerF)
open GaussianRationalLowerBounds (lower lower_congr lower_from_representation product_lower)
open GaussianRootAlgebra (equal equal_of_values re_mul im_mul re_one im_one)
open ComplexLogarithmRemainder (oneCode normSq_one)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameReciprocal (apart anchor)
open GaussianCyclicExponentialSamples (inverseBudget exponential_lower)
open GaussianNamedSmallPerturbationTransport (productClock product_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def translatedValue (z B m : PTm n) : PTm n := ofGaussian (translated z B m) B
def translatedPower (z B m : PTm n) : PTm n := power (translatedValue z B m) m
def inverseInteger (m : PTm n) : PTm n := ofGaussian oneCode m
def inversePower (m : PTm n) : PTm n := power (inverseInteger m) m

def nameF : PR 2 := multiplyF constantF exponentialF
def data (z R B m : PTm n) : PTm n :=
  multiplyData constantF exponentialF (inversePower m) (exponentialData z R B m)
def factorizedF : PR 2 := multiplyF constantF nameF
def factorizedData (z R B m : PTm n) : PTm n :=
  multiplyData constantF nameF (translatedPower z B m) (data z R B m)
def multiplierSample (p z R B m : PTm n) : PTm n :=
  qmul (inversePower m) (ap2 exponentialF p (exponentialData z R B m))

def height (R m : PTm n) : PTm n := minimumClock R+GaussianRootSchedule.binaryLength (denominator R m m)

@[simp] theorem subst_translatedPower {l : ℕ} (σ : Fin n → PTm l) (z B m : PTm n) :
    Syn.subst σ (translatedPower z B m) = translatedPower (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ m) := by
  simp [translatedPower,translatedValue]

@[simp] theorem subst_inversePower {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (inversePower m) = inversePower (Syn.subst σ m) := by
  simp [inversePower,inverseInteger,oneCode,one]

@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z R B m : PTm n) :
    Syn.subst σ (data z R B m) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) := by
  simp [data]

theorem base_factor (z B m : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] base z B m ≐ qmul (translatedValue z B m) (inverseInteger m) := by
  let a := translated z B m
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul a oneCode) a := by
    apply equal_of_values <;> simp only [re_mul,im_mul,re_one,im_one] <;> ring
  have hr := qmul_represents (translatedValue z B m) (inverseInteger m) a oneCode B m hB hm
    (ofGaussian_represents a B hB) (ofGaussian_represents oneCode m hm)
  exact canonical_unique _ _ a (B*m) (GaussianRationalHorner.qadd_canonical _ _) (qmul_canonical _ _)
    (positive_product _ _ hB hm) (GaussianBarnesCanonicalBase.base_represents z B m hB hm)
    (represents_congr (.eqRefl _) e (.eqRefl _) hr)

theorem power_factor (z B m : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] powerValue z B m ≐ qmul (translatedPower z B m) (inversePower m) :=
  (congrAp2 powerF (.eqRefl m) (base_factor z B m hB hm)).eqTrans (power_product _ _ m)

theorem original_sample_factor (p z R B m : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] ap2 GaussianBarnesCanonicalFactor.nameF p (GaussianBarnesCanonicalFactor.data z R B m) ≐
      qmul (translatedPower z B m) (multiplierSample (GaussianBarnesCanonicalFactor.clock p z R B m) z R B m) :=
  (GaussianBarnesCanonicalFactor.sample_at p z R B m).eqTrans
    ((qmul_congr (power_factor z B m hB hm) (.eqRefl _)).eqTrans (qmul_associative _ _ _))

theorem regular (z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B m) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianBarnesCanonicalFactor.exponential_input z R B m h))

theorem factor_cross (z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] crossEquivalent GaussianBarnesCanonicalFactor.nameF factorizedF
      (GaussianBarnesCanonicalFactor.data z R B m) (factorizedData z R B m) := by
  let a := translatedPower z B m
  let b := inversePower m
  let c := powerValue z B m
  let x := exponentialData z R B m
  let C := multiplyF constantF constantF
  let d := multiplyData constantF constantF a b
  have hx := GaussianRadiusExponentialName.name_regular _ _ _ (GaussianBarnesCanonicalFactor.exponential_input z R B m h)
  have hd : Γ ⊢[PRAAx] pointCN C d :=
    multiply_fast constantF constantF a b (constant_regular a) (constant_regular b)
  have hc := GaussianGammaDigammaTwoShiftNamedSize.constant_product a b c (power_factor z B m h.andE₁ h.andE₂.andE₁).eqSymm
  have e := GaussianGammaAdjacentCutoff.multiply_cross constantF C exponentialF exponentialF c d x x
    (constant_regular c) hd hx hx (cross_symm C constantF d c hc) (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ _ _ e
    (GaussianNameRingLaws.multiply_associative constantF constantF exponentialF a b x (constant_regular a) (constant_regular b) hx)

theorem multiplier_sample_at (p z R B m : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B m) ≐
      multiplierSample (productClock constantF exponentialF (inversePower m) (exponentialData z R B m) p) z R B m := by
  let t := productClock constantF exponentialF (inversePower m) (exponentialData z R B m) p
  exact (product_at constantF exponentialF (inversePower m) (exponentialData z R B m) p).eqTrans
    (qmul_congr (constant_at t (inversePower m)) (.eqRefl _))

private theorem inverse_integer_lower (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] lower (inverseInteger m) one m :=
  lower_from_representation _ _ _ _ _ hm hm (ofGaussian_represents oneCode m hm)
    (le_congr (by ipra_ring) (congrMul (.eqRefl (m*m)) normSq_one).eqSymm (le_refl (m*m*one)))

theorem multiplier_lower (p z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m)
    (hp : Γ ⊢[PRAAx] le (minimumClock R) p) :
    Γ ⊢[PRAAx] lower (ap2 nameF p (data z R B m)) one (denominator R m m) := by
  let S := exponentRadius R
  let t := productClock constantF exponentialF (inversePower m) (exponentialData z R B m) p
  have ht : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have cap : Γ ⊢[PRAAx] le (two*inverseBudget S) (unit (minimumClock R)) :=
    (GaussianRootSchedule.binary_length_correct (two*inverseBudget S)).andE₁
  have ex := exponential_lower constantF S (correction z B m) t (GaussianBarnesCanonicalFactor.exponential_input z R B m h)
    (le_trans cap (GaussianBalancedRadiusArithmetic.unit_monotone (minimumClock R) t (le_trans hp ht)))
  have inv := power_lower (inverseInteger m) m m h.andE₂.andE₁ (inverse_integer_lower m h.andE₂.andE₁)
  have expDen := positive_product (Γ := Γ) two (GaussianCyclicExponentialSamples.sampleBound S) (le_succ_self one)
    (GaussianFactorBudget.power_positive (num 3) S (le_trans (le_succ_self one) (le_succ_self two)))
  exact lower_congr (multiplier_sample_at p z R B m).eqSymm (one_mul one) (.eqRefl _)
    (product_lower _ _ one _ one _ (GaussianFactorBudget.power_positive m m h.andE₂.andE₁) expDen inv ex)

theorem original_apart (z R B m : PTm n) (h : Γ ⊢[PRAAx] source z R B m) :
    Γ ⊢[PRAAx] apart nameF (height R m) (data z R B m) := by
  let D := denominator R m m
  let H := height R m
  let p := anchor H
  have hp : Γ ⊢[PRAAx] le (minimumClock R) p := le_trans (le_add_right _ _) (le_add_right _ _)
  have hD : Γ ⊢[PRAAx] le D (unit H) :=
    le_trans (GaussianRootSchedule.binary_length_correct D).andE₁
      (GaussianBalancedRadiusArithmetic.unit_monotone (GaussianRootSchedule.binaryLength D) H (le_add_left _ _))
  exact GaussianNamedFiniteProductApartness.weaken_margin _ D (unit H) (denominator_positive R m m h.andE₂.andE₁) hD
    (multiplier_lower p z R B m h hp)

theorem actual_Barnes_factor_deflation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let m := var 3
     source z R B m ⟶
       crossEquivalent GaussianBarnesCanonicalFactor.nameF factorizedF
         (GaussianBarnesCanonicalFactor.data z R B m) (factorizedData z R B m) ⋏
       apart nameF (height R m) (data z R B m)) :=
  closeUniv 4 (.impI (.andI (factor_cross _ _ _ _ Prf.hyp0) (original_apart _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDeflatedFactor
