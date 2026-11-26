import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaGaussEulerProduct
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaGaussReferenceEulerProduct
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGaussMultiplicationSharpPowerRate
import IPRADerivations.Analysis.Exponential.GaussianRobinMeshExponential

/-!
# Cofinal observations for the Gauss multiplication formula

One cutoff pays for both finite products, the two scaled-cutoff Euler
observations, and the sharp logarithmic power comparison. All bounds
use the literal finite programs at that cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationCofinalRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaGaussDomain (scaledRadius)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianGaussEulerCutoff (commonCutoff common_guards larger_cutoff_error scaled_cutoff_later)
open GaussianGaussMultiplicationPowerRate (amplification powerF)
open GaussianGaussMultiplicationPowerPerturbation (rowData limitData)
open GaussianGaussMultiplicationSharpPowerRate (coefficient sharp_rate)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)
local notation "needed" => GaussianGammaEulerInverseApproximationName.cutoff

def cutoff (p R m a d : PTm n) : PTm n :=
  commonCutoff p R m a d+(needed p one one one+(coefficient R m*unit p+amplification R m))

def scaledCutoff (p R m a d : PTm n) : PTm n := GaussianGammaGaussEulerHeads.cutoff m (cutoff p R m a d)
def shiftedSample (p z R B m a d : PTm n) : PTm n :=
  GaussianGammaGaussEulerProduct.sample p z R B m d (cutoff p R m a d)
def referenceSample (p R m a d : PTm n) : PTm n :=
  GaussianGammaGaussReferenceEulerProduct.sample p m (cutoff p R m a d)
def scaledSample (p z R B m a d : PTm n) : PTm n :=
  ap2 eulerF (succ p) (eulerData (scale m z) (scaledRadius R m) B d (scaledCutoff p R m a d))
def unitSample (p R m a d : PTm n) : PTm n :=
  ap2 eulerF (succ p) (eulerData oneCode one one one (scaledCutoff p R m a d))
def powerSample (p z R B m a d : PTm n) : PTm n :=
  ap2 powerF p (rowData z R B m (cutoff p R m a d))
def scaledData (z R B m d : PTm n) : PTm n := gammaData (scale m z) (scaledRadius R m) B d

@[simp] theorem subst_cutoff {l : ℕ} (σ : Fin n → PTm l) (p R m a d : PTm n) :
    Syn.subst σ (cutoff p R m a d) = cutoff (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) :=
  by simp [cutoff,one]
@[simp] theorem subst_scaledCutoff {l : ℕ} (σ : Fin n → PTm l) (p R m a d : PTm n) :
    Syn.subst σ (scaledCutoff p R m a d) =
      scaledCutoff (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [scaledCutoff]
@[simp] theorem subst_shiftedSample {l : ℕ} (σ : Fin n → PTm l) (p z R B m a d : PTm n) :
    Syn.subst σ (shiftedSample p z R B m a d) = shiftedSample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [shiftedSample]
@[simp] theorem subst_referenceSample {l : ℕ} (σ : Fin n → PTm l) (p R m a d : PTm n) :
    Syn.subst σ (referenceSample p R m a d) =
      referenceSample (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [referenceSample]
@[simp] theorem subst_scaledSample {l : ℕ} (σ : Fin n → PTm l) (p z R B m a d : PTm n) :
    Syn.subst σ (scaledSample p z R B m a d) = scaledSample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [scaledSample]
@[simp] theorem subst_unitSample {l : ℕ} (σ : Fin n → PTm l) (p R m a d : PTm n) :
    Syn.subst σ (unitSample p R m a d) =
      unitSample (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [unitSample,one]
@[simp] theorem subst_powerSample {l : ℕ} (σ : Fin n → PTm l) (p z R B m a d : PTm n) :
    Syn.subst σ (powerSample p z R B m a d) = powerSample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [powerSample]
@[simp] theorem subst_scaledData {l : ℕ} (σ : Fin n → PTm l) (z R B m d : PTm n) :
    Syn.subst σ (scaledData z R B m d) = scaledData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) (Syn.subst σ d) :=
  by simp [scaledData]

private theorem base_later (p R m a d : PTm n) : Γ ⊢[PRAAx] le (commonCutoff p R m a d) (cutoff p R m a d) :=
  le_add_right _ _

theorem cutoff_positive (p R m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le one (cutoff p R m a d) :=
  le_trans (common_guards p R m a d hm).andE₁ (base_later p R m a d)

theorem shifted_cutoff (p R m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le (GaussianGammaGaussEulerProduct.threshold p R m a d) (cutoff p R m a d) :=
  le_trans (common_guards p R m a d hm).andE₂.andE₁ (base_later p R m a d)

theorem reference_cutoff (p R m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le (GaussianGammaGaussReferenceEulerProduct.threshold p m) (cutoff p R m a d) :=
  le_trans (common_guards p R m a d hm).andE₂.andE₂.andE₂ (base_later p R m a d)

theorem scaled_cutoff (p R m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le (needed p (scaledRadius R m) a d) (scaledCutoff p R m a d) := by
  have base : Γ ⊢[PRAAx] le (needed p (scaledRadius R m) a d) (commonCutoff p R m a d) := by
    exact le_of_eq_add
      (d := needed p (R+one) a (d*m)+needed p one one m+one)
      (by unfold commonCutoff; ipra_ring)
  exact le_trans base (le_trans (base_later p R m a d) (scaled_cutoff_later m _ hm))

theorem unit_cutoff (p R m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le (needed p one one one) (scaledCutoff p R m a d) := by
  have base : Γ ⊢[PRAAx] le (needed p one one one) (cutoff p R m a d) :=
    le_trans (le_add_right _ _) (le_add_left _ _)
  exact le_trans base (scaled_cutoff_later m _ hm)

theorem power_cutoff (p R m a d : PTm n) : Γ ⊢[PRAAx]
    le (amplification R m) (cutoff p R m a d) ⋏ le (coefficient R m*unit p) (cutoff p R m a d) := by
  have bigger : Γ ⊢[PRAAx] le (coefficient R m*unit p+amplification R m) (cutoff p R m a d) :=
    le_trans (le_add_left _ _) (le_add_left _ _)
  exact .andI (le_trans (le_add_left _ _) bigger) (le_trans (le_add_right _ _) bigger)

theorem scaled_regular (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] pointCN gammaF (scaledData z R B m d) :=
  GaussianGammaReciprocalInverse.gamma_regular _ _ _ _ _ h.andE₂

theorem limit_power_regular (z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] pointCN powerF (limitData z R B m) :=
  GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianGaussMultiplicationPowerRate.limit_power_input z R B m h.andE₁.andE₁ h.andE₂.andE₁.andE₂.andE₁ h.andE₁.andE₂)

private theorem diagonal_bound (x y A p : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded x y (A*(unit p+unit p)) (unit p*unit p)) : Γ ⊢[PRAAx]
    distanceBounded x y (two*A) (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := zero) (by ipra_ring)) h

theorem shifted_error (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] distanceBounded (shiftedSample p z R B m a d)
      (ap2 GaussianGammaGaussShiftedProduct.nameF p (GaussianGammaGaussShiftedProduct.data z R B m d))
      (two*GaussianGammaGaussEulerProduct.errorBudget R m d) (unit p) :=
  diagonal_bound _ _ _ p (GaussianGammaGaussEulerProduct.product_error p p z R B m a d _ h
    (shifted_cutoff p R m a d h.andE₁.andE₁))

theorem reference_error (p R m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] distanceBounded (referenceSample p R m a d)
      (ap2 GaussianGammaGaussReferenceProduct.nameF p (GaussianGammaGaussReferenceProduct.data m))
      (two*GaussianGammaGaussReferenceEulerProduct.errorBudget m) (unit p) :=
  diagonal_bound _ _ _ p (GaussianGammaGaussReferenceEulerProduct.product_error p p m _ (reference_cutoff p R m a d hm))

theorem scaled_error (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] distanceBounded (scaledSample p z R B m a d) (ap2 gammaF p (scaledData z R B m d)) two (unit p) := by
  have h0 := larger_cutoff_error p p _ _ _ a d _ h.andE₂ (scaled_cutoff p R m a d h.andE₁.andE₁)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) (diagonal_bound _ _ one p
    (distance_congr (.eqRefl _) (.eqRefl _) (one_mul _).eqSymm (.eqRefl _) h0))

theorem unit_error (p R m a d : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] distanceBounded (unitSample p R m a d) qone (num 4) (unit p) := by
  let x := gammaData (oneCode : PTm n) one one one
  have first := larger_cutoff_error p p oneCode one one one one (scaledCutoff p R m a d)
    GaussianGammaNormalization.unit_gamma_source (unit_cutoff p R m a d hm)
  have next := GaussianNameEquivalence.cross_at (Γ := Γ) gammaF GaussianNameRingLaws.oneF x zero p p
    GaussianRobinMeshExponential.C21_Gamma_one
  have first' : Γ ⊢[PRAAx] distanceBounded (unitSample p R m a d) (ap2 gammaF p x) two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p))
      (unit_positive p) (le_of_eq_add (d := zero) (by ipra_ring)) first
  have next' : Γ ⊢[PRAAx] distanceBounded (ap2 gammaF p x) qone two (unit p) :=
    distance_congr (.eqRefl _) (GaussianNameRingLaws.one_at p zero) (.eqRefl _) (.eqRefl _)
      (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p))
        (unit_positive p) (le_of_eq_add (d := zero) (by ipra_ring)) next)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first' next')

theorem power_error (p z R B m a d : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] distanceBounded (powerSample p z R B m a d) (ap2 powerF p (limitData z R B m)) (num 3) (unit p) := by
  let N := cutoff p R m a d
  let C := coefficient R m
  let U := unit p
  have hm := h.andE₁.andE₁
  have hn := cutoff_positive p R m a d hm
  have paid := (power_cutoff (Γ := Γ) p R m a d).andE₂
  have raw := GaussianNamedInverseRate.diagonal_rate powerF powerF (rowData z R B m N) (limitData z R B m) C N p hn
    (sharp_rate z R B m N hm hn (power_cutoff p R m a d).andE₁ h.andE₂.andE₁.andE₂.andE₁ h.andE₁.andE₂)
  have leR : Γ ⊢[PRAAx] le ((C*U+two*N)*U) (num 3*(N*U)) := by ipra_le 𝔞 U*sl paid
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hn (unit_positive p)) (unit_positive p) leR raw

end LeanProofs.IPRA.Analysis.GaussianGaussMultiplicationCofinalRows
