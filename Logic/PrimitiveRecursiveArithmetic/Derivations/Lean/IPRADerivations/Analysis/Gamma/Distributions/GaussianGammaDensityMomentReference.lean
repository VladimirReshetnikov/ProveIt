import IPRADerivations.Analysis.Gamma.Distributions.GaussianGammaDensityDomain

/-!
# Normalized original shifted Euler quadrature and its moment value

One original C7 observation normalizes the unchanged original Euler
quadrature at z/B+N. The actual regular product has value (z/B)_N by
source-derived V8 and actual inverse cancellation. Its literal unchanged
quadrature readback is retained; binding its rows to the base density
times t^N is a separate finite observation comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDensityMomentReference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (source original_Euler_integral_is_Gamma improper_source)
open GaussianGammaShiftTrajectory (point)
open GaussianGammaRepeatedShift (risingProduct)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaReciprocalInverse (gammaF gammaData gamma_regular gamma_product)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans cross_symm cross_at)
open GaussianNameRingLaws (oneF)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianCoefficientNameBounds (unit)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "P" => GaussianGammaC7Name.nameF
local notation "I" => GaussianEulerImproperName.nameF

def baseData (z R B : PTm n) : PTm n := GaussianGammaC7Name.data z R B
def shiftedData (z R B A N : PTm n) : PTm n := GaussianEulerImproperName.data (point z B N) (R+N) B A
def nameF : PR 2 := multiplyF P I
def data (z R B A N : PTm n) : PTm n := multiplyData P I (baseData z R B) (shiftedData z R B A N)
def clock (p z R B A N : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus P I (baseData z R B) (shiftedData z R B A N)) p
@[simp] theorem subst_baseData {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (baseData z R B) = baseData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [baseData]
@[simp] theorem subst_shiftedData {m : ℕ} (σ : Fin n → PTm m) (z R B A N : PTm n) :
    Syn.subst σ (shiftedData z R B A N) = shiftedData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ N) := by simp [shiftedData]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B A N : PTm n) :
    Syn.subst σ (data z R B A N) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ N) := by simp [data]
@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p z R B A N : PTm n) :
    Syn.subst σ (clock p z R B A N) = clock (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ N) := by simp [clock]

theorem base_regular (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx] pointCN P (baseData z R B) :=
  GaussianGammaC7Name.name_regular _ _ _ (GaussianGammaDensityDomain.base_gamma_source z R B A h).andE₁
theorem shifted_regular (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx] pointCN I (shiftedData z R B A N) :=
  GaussianEulerImproperName.name_regular _ _ _ _ (improper_source _ _ _ _ (GaussianGammaDensityDomain.shifted_source z R B A N h))
theorem name_regular (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx] pointCN nameF (data z R B A N) :=
  multiply_fast _ _ _ _ (base_regular z R B A h) (shifted_regular z R B A N h)

theorem original_value (z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    crossEquivalent nameF constantF (data z R B A N) (risingProduct z B N) := by
  let Z := baseData z R B
  let S := shiftedData z R B A N
  let G := gammaData z R B A
  let H := gammaData (point z B N) (R+N) B A
  let F := risingProduct z B N
  have hp := base_regular z R B A h
  have hi := shifted_regular z R B A N h
  have hg := gamma_regular _ _ _ _ _ (GaussianGammaDensityDomain.base_gamma_source z R B A h)
  have hh := gamma_regular _ _ _ _ _ (GaussianGammaDensityDomain.shifted_gamma_source z R B A N h)
  have hc := constant_regular (Γ := Γ) F
  have hr := GaussianGammaRisingFactorial.rising_regular z R B one A N (GaussianGammaDensityDomain.base_gamma_source z R B A h)
  have first := GaussianGammaAdjacentCutoff.multiply_cross P P I gammaF Z Z S H hp hp hi hh
    (cross_refl _ _ hp) (original_Euler_integral_is_Gamma _ _ _ _ (GaussianGammaDensityDomain.shifted_source z R B A N h))
  have second := GaussianGammaAdjacentCutoff.multiply_cross P P gammaF GaussianGammaRisingFactorial.risingF Z Z H
    (GaussianGammaRisingFactorial.risingData z R B A N) hp hp hh hr (cross_refl _ _ hp)
    (GaussianGammaRisingFactorial.original_Gamma_rising_factorial z R B one A one A N (GaussianGammaDensityDomain.rising_input z R B A N h))
  have firstAssoc := GaussianNameRingLaws.multiply_associative P constantF gammaF Z F G hp hc hg
  have swap := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF P constantF) (multiplyF constantF P) gammaF gammaF
    (multiplyData P constantF Z F) (multiplyData constantF P F Z) G G
    (multiply_fast _ _ _ _ hp hc) (multiply_fast _ _ _ _ hc hp) hg hg
    (GaussianNameRingLaws.multiply_commutative P constantF Z F hp hc) (cross_refl _ _ hg)
  have secondAssoc := GaussianNameRingLaws.multiply_associative constantF P gammaF F Z G hc hp hg
  have unitRegular := GaussianNameRingLaws.one_fast (Γ := Γ) F
  have unitProduct := cross_trans _ _ _ _ _ _ (gamma_product z R B one A (GaussianGammaDensityDomain.base_gamma_source z R B A h))
    (GaussianBoundedInverseApartness.ones_equivalent Z F)
  have cancel := GaussianGammaAdjacentCutoff.multiply_cross constantF constantF (multiplyF P gammaF) oneF F F
    (multiplyData P gammaF Z G) F hc hc (multiply_fast _ _ _ _ hp hg) unitRegular (cross_refl _ _ hc) unitProduct
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ second
    (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ firstAssoc) (cross_trans _ _ _ _ _ _ swap
      (cross_trans _ _ _ _ _ _ secondAssoc (cross_trans _ _ _ _ _ _ cancel (GaussianNameRingLaws.multiply_one constantF F hc))))))

theorem sample_at (p z R B A N : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data z R B A N) ≐ qmul (GaussianGammaC7Name.sample (clock p z R B A N) z R B)
      (ap2 I (clock p z R B A N) (shiftedData z R B A N)) :=
  (GaussianNameArithmetic.multiply_at P I _ _ p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))

theorem original_observations (p q z R B A N : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B A N)) (ap2 constantF q (risingProduct z B N))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_value z R B A N h)

theorem actual_original_normalized_shifted_Euler_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent nameF constantF
      (data (var 0) (var 1) (var 2) (var 3) (var 4)) (risingProduct (var 0) (var 2) (var 4))) :=
  closeUniv 5 (.impI (original_value _ _ _ _ _ Prf.hyp0))
theorem actual_original_normalized_shifted_Euler_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5)) ≐
      qmul (GaussianGammaC7Name.sample (clock (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 1) (var 2) (var 3))
        (ap2 I (clock (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (shiftedData (var 1) (var 2) (var 3) (var 4) (var 5)))) :=
  closeUniv 6 (sample_at _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaDensityMomentReference
