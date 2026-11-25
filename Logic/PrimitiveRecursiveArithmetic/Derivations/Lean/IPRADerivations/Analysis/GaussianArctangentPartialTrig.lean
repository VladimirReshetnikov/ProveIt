import IPRADerivations.Analysis.GaussianArctangentCayleyTrig
import IPRADerivations.Analysis.GaussianArctangentPartialExponential
import IPRADerivations.Analysis.GaussianGammaEulerShift

/-!
# Original named sine and cosine on the rational arctangent interval

The original positive and negative exponentials at twice the partial
arctangent supply the Cayley value and its conjugate. The literal named
difference and sum give the two rational expressions in (T1).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentPartialTrig

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentCayleyStep (conjugateValue)
open GaussianArctangentCayleyValues (value)
open GaussianArctangentCayleyTrig (cosineMultiplier sinePoint cosinePoint conjugate_inverse sine_readback cosine_readback
  linearPoint conjugateLinearPoint quotient_readback)
open GaussianArctangentPartialQuadrature (nameF data)
open GaussianArctangentPartialExponential (exponentialF exponentialData exponential_cross exponential_input)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerShift (constant_sum_cross)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedSineFromExponential (sineF sineData sine_constant negative_exponential_constant)
open GaussianNameArithmetic (addF addData add_equivalent add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal cross_trans)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianRationalHorner (qadd qmul)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cosineSumF (f : PR 2) : PR 2 :=
  addF (GaussianRadiusExponentialName.nameF f) (GaussianRadiusExponentialName.nameF (negativeF f))
def cosineSumData (R x : PTm n) : PTm n :=
  addData (GaussianRadiusExponentialName.data R x) (GaussianRadiusExponentialName.data R (negativeData x))
def cosineF (f : PR 2) : PR 2 := multiplyF constantF (cosineSumF f)
def cosineData (f : PR 2) (R x : PTm n) : PTm n := multiplyData constantF (cosineSumF f) cosineMultiplier (cosineSumData R x)

@[simp] theorem subst_cosineSumData {m : ℕ} (σ : Fin n → PTm m) (R x : PTm n) :
    Syn.subst σ (cosineSumData R x) = cosineSumData (Syn.subst σ R) (Syn.subst σ x) := by simp [cosineSumData]

@[simp] theorem subst_cosineData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (R x : PTm n) :
    Syn.subst σ (cosineData f R x) = cosineData f (Syn.subst σ R) (Syn.subst σ x) := by simp [cosineData]

theorem cosine_regular (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) :
    Γ ⊢[PRAAx] pointCN (cosineF f) (cosineData f R x) :=
  multiply_fast _ _ _ _ (constant_regular _) (add_fast _ _ _ _
    (GaussianRadiusExponentialName.name_regular _ _ _ h)
    (GaussianRadiusExponentialName.name_regular _ _ _ (GaussianExponentialInverse.negative_input f R x h)))

theorem cosine_constant (f : PR 2) (R x a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x)
    (ha : Γ ⊢[PRAAx] crossEquivalent (GaussianRadiusExponentialName.nameF f) constantF
      (GaussianRadiusExponentialName.data R x) a)
    (hb : Γ ⊢[PRAAx] crossEquivalent (GaussianRadiusExponentialName.nameF (negativeF f)) constantF
      (GaussianRadiusExponentialName.data R (negativeData x)) b) :
    Γ ⊢[PRAAx] crossEquivalent (cosineF f) constantF (cosineData f R x) (qmul cosineMultiplier (qadd a b)) := by
  have he := GaussianRadiusExponentialName.name_regular _ _ _ h
  have hn := GaussianRadiusExponentialName.name_regular _ _ _ (GaussianExponentialInverse.negative_input f R x h)
  have hconst := constant_regular (Γ := Γ) cosineMultiplier
  have hs := add_equivalent _ _ _ _ _ _ _ _ he (constant_regular a) hn (constant_regular b)
    (cross_to_diagonal _ _ _ _ ha) (cross_to_diagonal _ _ _ _ hb)
  have reduce := cross_trans _ _ _ _ _ _ hs (constant_sum_cross a b)
  have product := multiply_cross _ _ _ _ _ _ _ _ hconst hconst (add_fast _ _ _ _ he hn)
    (constant_regular _) (cross_refl _ _ hconst) reduce
  exact cross_trans _ _ _ _ _ _ product (constant_product_cross cosineMultiplier (qadd a b))

theorem conjugate_exponential_cross (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianRadiusExponentialName.nameF (negativeF nameF)) constantF
      (GaussianRadiusExponentialName.data two (negativeData (data A B))) (conjugateValue B A) :=
  negative_exponential_constant nameF two (data A B) (value B A) (conjugateValue B A)
    (exponential_input A B hB hA) (exponential_cross A B hB hA) (conjugate_inverse B A hB)

theorem sine_cross (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] crossEquivalent (sineF nameF) constantF (sineData nameF two (data A B)) (sinePoint B A) :=
  cross_trans _ _ _ _ _ _
    (sine_constant _ _ _ _ _ (exponential_input A B hB hA)
      (exponential_cross A B hB hA) (conjugate_exponential_cross A B hB hA))
    (constant_data_cross _ _ (sine_readback B A hB))

theorem cosine_cross (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] crossEquivalent (cosineF nameF) constantF (cosineData nameF two (data A B)) (cosinePoint B A) :=
  cross_trans _ _ _ _ _ _
    (cosine_constant _ _ _ _ _ (exponential_input A B hB hA)
      (exponential_cross A B hB hA) (conjugate_exponential_cross A B hB hA))
    (constant_data_cross _ _ (cosine_readback B A hB))

def quotientProductF : PR 2 := multiplyF exponentialF constantF
def quotientProductData (A B : PTm n) : PTm n :=
  multiplyData exponentialF constantF (exponentialData A B) (conjugateLinearPoint B A)

theorem quotient_cross (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B) :
    Γ ⊢[PRAAx] crossEquivalent quotientProductF constantF (quotientProductData A B) (linearPoint B A) := by
  have reg := GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input A B hB hA)
  have den := constant_regular (Γ := Γ) (conjugateLinearPoint B A)
  have m := multiply_cross _ _ _ _ _ _ _ _ reg (constant_regular (value B A)) den den
    (exponential_cross A B hB hA) (cross_refl _ _ den)
  exact cross_trans _ _ _ _ _ _ m
    (cross_trans _ _ _ _ _ _ (constant_product_cross (value B A) (conjugateLinearPoint B A))
      (constant_data_cross _ _ (quotient_readback B A hB)))

theorem actual_rational_arctangent_Cayley_quotient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶
      crossEquivalent quotientProductF constantF (quotientProductData (var 0) (var 1)) (linearPoint (var 1) (var 0))) :=
  closeUniv 2 (.impI (.impI (quotient_cross _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_rational_arctangent_sine_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶
      crossEquivalent (sineF nameF) constantF (sineData nameF two (data (var 0) (var 1))) (sinePoint (var 1) (var 0))) :=
  closeUniv 2 (.impI (.impI (sine_cross _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_rational_arctangent_cosine_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶
      crossEquivalent (cosineF nameF) constantF (cosineData nameF two (data (var 0) (var 1)))
        (cosinePoint (var 1) (var 0))) :=
  closeUniv 2 (.impI (.impI (cosine_cross _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentPartialTrig
