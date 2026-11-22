import IPRADerivations.Analysis.GaussianEulerDecayAddition
import IPRADerivations.Analysis.GaussianEulerDecayOrder
import IPRADerivations.Analysis.GaussianNameRingLaws
import IPRADerivations.Analysis.RationalConvexClockRescale

/-!
# The two actual half-decay factors in the Euler integrand

The doubled denominator represents half the original positive time.
Addition of those two encoded times normalizes to the original
decay input. This identifies the actual product name and gives its
observation comparison with independent requested precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerHalfDecayProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianEulerDecayOrder (signedTime signed_time_embedding)
open GaussianEuclideanDistanceName (fraction)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans cross_refl)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def halfProductData (a b : PTm n) : PTm n :=
  multiplyData decayF decayF (decayData a (two*b)) (decayData a (two*b))

@[simp] theorem subst_halfProductData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (halfProductData a b) = halfProductData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [halfProductData,decayData,exponentialInputData]

theorem doubled_time_fraction (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] fraction (a*(two*b)+a*(two*b)) ((two*b)*(two*b)) ≐ fraction a b := by
  have h2 : Γ ⊢[PRAAx] le one two := le_succ_self one
  have h := positive_product _ _ h2 (positive_product _ _ h2 hb)
  exact (RationalNonnegativePowers.fraction_congr (by ipra_ring) (by ipra_ring)).eqTrans
    (RationalConvexClockRescale.fraction_rescale a b (two*(two*b)) hb h)

theorem doubled_decay_input (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] decayData (a*(two*b)+a*(two*b)) ((two*b)*(two*b)) ≐ decayData a b := by
  let D := two*b
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (le_succ_self one) hb
  have h := doubled_time_fraction a b hb
  have e : Γ ⊢[PRAAx] decayPoint (a*D+a*D) (D*D) ≐ decayPoint a b :=
    (signed_time_embedding _ _ (positive_product _ _ hD hD)).eqSymm.eqTrans
      ((RationalGaussianRealPart.embed_congr (RationalAlgebra.negative_congr h)).eqTrans
        (signed_time_embedding a b hb))
  simpa only [decayData,exponentialInputData,GaussianRadiusExponentialName.subst_data,
    GaussianNameBounds.subst_U,Syn.subst_var,Matrix.cons_val_zero] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (exponentialInputData constantF (var 0) : PTm 1)
      (σ := ![decayPoint (a*D+a*D) (D*D)]) (σ' := ![decayPoint a b]) (fun i => by fin_cases i; exact e)

private theorem cross_right_congr (F G : PR 2) (x y z : PTm n)
    (e : Γ ⊢[PRAAx] y ≐ z) (h : Γ ⊢[PRAAx] crossEquivalent F G x y) :
    Γ ⊢[PRAAx] crossEquivalent F G x z := by
  have result := Prf.eqSubst (Γ := Γ) (Ax := PRAAx)
    (crossEquivalent F G (var 0) (var 1) : Fm PTm 2) ![x,y] ![x,z]
    (fun i => by fin_cases i; exact .eqRefl _; exact e)
    (by simpa only [GaussianNameEquivalence.subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using h)
  simpa only [GaussianNameEquivalence.subst_crossEquivalent,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using result

theorem original_decay_as_half_product (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF decayF decayF) decayF (halfProductData a b) (decayData a b) := by
  let D := two*b
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (le_succ_self one) hb
  exact cross_right_congr _ _ (halfProductData a b) (decayData (a*D+a*D) (D*D)) (decayData a b)
    (doubled_decay_input a b hb) (GaussianEulerDecayAddition.original_decay_add a D a D hD hD)

theorem independent_decay_observations (a b p q : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (multiplyF decayF decayF) p (halfProductData a b)) (ap2 decayF q (decayData a b))
      (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (original_decay_as_half_product a b hb)

theorem original_half_decay_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ crossEquivalent (multiplyF decayF decayF) decayF
      (halfProductData (var 0) (var 1)) (decayData (var 0) (var 1))) :=
  closeUniv 2 (.impI (original_decay_as_half_product _ _ Prf.hyp0))

open GaussianEulerIntegrandName (powerF powerData nameF data source productF productData)

def halfWeightedF : PR 2 := multiplyF powerF decayF
def halfWeightedData (z B a b : PTm n) : PTm n :=
  multiplyData powerF decayF (powerData z B a b) (decayData a (two*b))
def halfIntegrandF : PR 2 := multiplyF halfWeightedF decayF
def halfIntegrandData (z B a b : PTm n) : PTm n :=
  multiplyData halfWeightedF decayF (halfWeightedData z B a b) (decayData a (two*b))

@[simp] theorem subst_halfWeightedData {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (halfWeightedData z B a b) =
      halfWeightedData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [halfWeightedData,decayData,exponentialInputData]

@[simp] theorem subst_halfIntegrandData {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (halfIntegrandData z B a b) =
      halfIntegrandData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [halfIntegrandData,decayData,exponentialInputData]

theorem decay_regular (a b : PTm n) : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN decayF (decayData a b) := by
  exact GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianGammaFiniteApproximantName.exponential_input constantF (decayPoint a b) (GaussianGammaCanonicalExponent.constant_regular _))

theorem original_integrand_half_decay_factors (z B a b : PTm n) (h : Γ ⊢[PRAAx] source z B a b) :
    Γ ⊢[PRAAx] crossEquivalent halfIntegrandF nameF (halfIntegrandData z B a b) (data z B a b) := by
  let P := powerData z B a b
  let D := decayData a (two*b)
  let E := decayData a b
  let D2 := halfProductData a b
  have hp := GaussianEulerIntegrandName.power_regular z B a b h
  have hd := decay_regular (Γ := Γ) a (two*b)
  have he := decay_regular (Γ := Γ) a b
  have hs := GaussianNameArithmetic.multiply_fast decayF decayF D D hd hd
  have part := GaussianGammaAdjacentCutoff.multiply_cross powerF powerF (multiplyF decayF decayF) decayF
    P P D2 E hp hp hs he (cross_refl powerF P hp) (original_decay_as_half_product a b h.andE₂.andE₂)
  exact cross_trans halfIntegrandF (multiplyF powerF (multiplyF decayF decayF)) nameF
    (halfIntegrandData z B a b) (multiplyData powerF (multiplyF decayF decayF) P D2) (data z B a b)
    (GaussianNameRingLaws.multiply_associative powerF decayF decayF P D D hp hd hd)
    (cross_trans _ productF _ _ (productData z B a b) _ part (GaussianEulerIntegrandName.original_power_times_decay z B a b h))

theorem original_Euler_integrand_half_factors_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent halfIntegrandF nameF
      (halfIntegrandData (var 0) (var 1) (var 2) (var 3)) (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_integrand_half_decay_factors _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerHalfDecayProduct
