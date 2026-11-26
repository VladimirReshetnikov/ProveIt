import IPRADerivations.Analysis.Gamma.EulerProducts.Factorials.GaussianGammaFallingFactorial

/-!
# The entire cleared reciprocal-Gamma form of V9

The literal falling numerator times P(z+1) equals P(z-N+1).
Factorial normalization therefore gives binomial(z,N) P(z+1)
=P(z-N+1)/N!, including every apparent cancelled pole. All samplers
are the original C7 names and actual normalized constant products.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaBinomialCleared

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFallingFactorial (start baseRadius endpointRadius fallingProduct factorialInverse binomial)
open GaussianGammaCanonicalExponent (source constantF constant_regular)
open GaussianGammaEulerHeadShift (shifted)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaC7Name.nameF

def baseData (z R B N : PTm n) : PTm n := GaussianGammaC7Name.data (start z B N) (baseRadius R N) B
def topData (z R B N : PTm n) : PTm n := GaussianGammaC7Name.data (shifted z B) (endpointRadius R N) B
def productF : PR 2 := multiplyF constantF P
def fallingData (z R B N : PTm n) : PTm n := multiplyData constantF P (fallingProduct z B N) (topData z R B N)
def binomialData (z R B N : PTm n) : PTm n := multiplyData constantF P (binomial z B N) (topData z R B N)
def inverseData (z R B N : PTm n) : PTm n := multiplyData constantF P (factorialInverse N) (baseData z R B N)

@[simp] theorem subst_baseData {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (baseData z R B N) = baseData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [baseData]
@[simp] theorem subst_topData {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (topData z R B N) = topData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [topData]
@[simp] theorem subst_fallingData {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (fallingData z R B N) = fallingData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [fallingData]
@[simp] theorem subst_binomialData {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (binomialData z R B N) = binomialData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [binomialData]
@[simp] theorem subst_inverseData {m : ℕ} (σ : Fin n → PTm m) (z R B N : PTm n) :
    Syn.subst σ (inverseData z R B N) = inverseData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [inverseData]

theorem base_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN P (baseData z R B N) :=
  GaussianGammaC7Name.name_regular _ _ _ (GaussianGammaFallingFactorial.start_source z R B N h)
theorem top_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN P (topData z R B N) :=
  GaussianGammaC7Name.name_regular _ _ _ (GaussianGammaFallingFactorial.endpoint_source z R B N h)
theorem falling_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN productF (fallingData z R B N) :=
  multiply_fast _ _ _ _ (constant_regular _) (top_regular z R B N h)
theorem binomial_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN productF (binomialData z R B N) :=
  multiply_fast _ _ _ _ (constant_regular _) (top_regular z R B N h)
theorem inverse_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] pointCN productF (inverseData z R B N) :=
  multiply_fast _ _ _ _ (constant_regular _) (base_regular z R B N h)

/-- The entire identity has no pole-separation or nonzero premise. -/
theorem original_entire_falling_identity (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent P productF (baseData z R B N) (fallingData z R B N) := by
  have hs := GaussianGammaFallingFactorial.start_source z R B N h
  have hp := GaussianGammaShiftTrajectory.point_source _ _ _ N hs
  have actual := GaussianGammaRepeatedShift.repeated_shift (start z B N) (baseRadius R N) B N hs
  have endpoint := GaussianGammaInputProperness.original_C7_proper _ _ _ _ hp
    (GaussianGammaFallingFactorial.endpoint_native z B N)
  have replacement := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF P P
    (fallingProduct z B N) (fallingProduct z B N)
    (GaussianGammaC7Name.data (GaussianGammaShiftTrajectory.point (start z B N) B N) (endpointRadius R N) B)
    (topData z R B N) (constant_regular _) (constant_regular _) (GaussianGammaC7Name.name_regular _ _ _ hp)
    (top_regular z R B N h) (cross_refl _ _ (constant_regular _)) endpoint
  exact cross_trans _ _ _ _ _ _ actual replacement

/-- V9 after clearing the possibly vanishing reciprocal-Gamma factor.
The finite binomial polynomial is evaluated by its original rational code. -/
theorem original_entire_binomial_identity (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent productF productF (binomialData z R B N) (inverseData z R B N) := by
  let c := factorialInverse N
  let F := fallingProduct z B N
  let T := topData z R B N
  let W := baseData z R B N
  have hc := constant_regular (Γ := Γ) c
  have hf := constant_regular (Γ := Γ) F
  have ht := top_regular z R B N h
  have hw := base_regular z R B N h
  have lifted := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF P productF c c W (fallingData z R B N)
    hc hc hw (falling_regular z R B N h) (cross_refl _ _ hc) (original_entire_falling_identity z R B N h)
  have assoc := GaussianNameRingLaws.multiply_associative constantF constantF P c F T hc hf ht
  have collapse := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF constantF constantF) constantF P P
    (multiplyData constantF constantF c F) (binomial z B N) T T
    (multiply_fast _ _ _ _ hc hf) (constant_regular _) ht ht
    (GaussianGammaWeierstrassApproximant.constant_product_cross c F) (cross_refl _ _ ht)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ lifted (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ assoc) collapse))

theorem original_observations (p q z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 productF p (binomialData z R B N)) (ap2 productF q (inverseData z R B N))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_entire_binomial_identity z R B N h)

theorem actual_original_entire_falling_reciprocal_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent P productF
      (baseData (var 0) (var 1) (var 2) (var 3)) (fallingData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_entire_falling_identity _ _ _ _ Prf.hyp0))
theorem actual_original_entire_binomial_V9_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ crossEquivalent productF productF
      (binomialData (var 0) (var 1) (var 2) (var 3)) (inverseData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (original_entire_binomial_identity _ _ _ _ Prf.hyp0))
theorem actual_original_entire_binomial_independent_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 2) (var 3) (var 4) ⟶
      distanceBounded (ap2 productF (var 0) (binomialData (var 2) (var 3) (var 4) (var 5)))
        (ap2 productF (var 1) (inverseData (var 2) (var 3) (var 4) (var 5)))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (original_observations _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaBinomialCleared
