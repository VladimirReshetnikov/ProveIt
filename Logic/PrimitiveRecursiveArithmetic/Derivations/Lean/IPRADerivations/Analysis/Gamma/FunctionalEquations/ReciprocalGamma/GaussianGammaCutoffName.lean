import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaC7Name

/-!
# The original C7 expression at an arbitrary valid numerical cutoff

The existing observation programs are retained. Only their persistent data
replace 2R by the actual runtime cutoff N. The original tail guard derives
regularity, and the original C7 data and observations at N=2R are literally
recovered. No independence of the cutoff is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCutoffName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qadd qmul)
open GaussianRationalMetric (bounded)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular productF productData productValue product_regular
  exponentF exponentialF addPrecision)
open GaussianGammaCanonicalTailName (source)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def exponentData (z R B N : PTm n) : PTm n := GaussianNameArithmetic.addData
  (productData z B N) (GaussianGammaCanonicalTailName.data z R B N)
def exponentPoint (p z R B N : PTm n) : PTm n := ap2 exponentF p (exponentData z R B N)
def exponentValue (p z R B N : PTm n) : PTm n := GaussianFastValueCut.recode
  (qadd (productValue (addPrecision p) z B N) (GaussianGammaCanonicalTailName.value (addPrecision p) z R B N))
def exponentRadius (z R B N : PTm n) : PTm n := GaussianNameBounds.U exponentF (exponentData z R B N)
def exponentialData (z R B N : PTm n) : PTm n := GaussianRadiusExponentialName.data
  (exponentRadius z R B N) (exponentData z R B N)
def exponentialPoint (p z R B N : PTm n) : PTm n := ap2 exponentialF p (exponentialData z R B N)
def head (z B N : PTm n) : PTm n := GaussianGammaEulerHead.run z B N
def nameF : PR 2 := GaussianGammaC7Name.nameF
def data (z R B N : PTm n) : PTm n := GaussianNameArithmetic.multiplyData constantF exponentialF
  (head z B N) (exponentialData z R B N)
def sample (p z R B N : PTm n) : PTm n := ap2 nameF p (data z R B N)
def samplePrecision (p z R B N : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF exponentialF (head z B N) (exponentialData z R B N)) p
def value (p z R B N : PTm n) : PTm n := GaussianFastValueCut.recode
  (qmul (head z B N) (exponentialPoint (samplePrecision p z R B N) z R B N))
def diskBound (z R B N : PTm n) : PTm n := GaussianNameBounds.U nameF (data z R B N)

@[simp] theorem subst_exponentData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (exponentData z R B N) = exponentData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exponentData]
@[simp] theorem subst_exponentPoint {l : ℕ} (σ : Fin n → PTm l) (p z R B N : PTm n) :
    Syn.subst σ (exponentPoint p z R B N) = exponentPoint (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exponentPoint]
@[simp] theorem subst_exponentRadius {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (exponentRadius z R B N) = exponentRadius (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exponentRadius]
@[simp] theorem subst_exponentialData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (exponentialData z R B N) = exponentialData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exponentialData]
@[simp] theorem subst_exponentialPoint {l : ℕ} (σ : Fin n → PTm l) (p z R B N : PTm n) :
    Syn.subst σ (exponentialPoint p z R B N) = exponentialPoint (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [exponentialPoint]
@[simp] theorem subst_head {l : ℕ} (σ : Fin n → PTm l) (z B N : PTm n) :
    Syn.subst σ (head z B N) = head (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp only [head,GaussianGammaEulerHead.run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (data z R B N) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [data]
@[simp] theorem subst_sample {l : ℕ} (σ : Fin n → PTm l) (p z R B N : PTm n) :
    Syn.subst σ (sample p z R B N) = sample (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [sample]
@[simp] theorem subst_diskBound {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (diskBound z R B N) = diskBound (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [diskBound]

theorem exponent_sample_at (p z R B N : PTm n) : Γ ⊢[PRAAx] exponentPoint p z R B N ≐ exponentValue p z R B N :=
  (GaussianNameArithmetic.add_at productF GaussianGammaCanonicalTailName.pointF (productData z B N)
    (GaussianGammaCanonicalTailName.data z R B N) p).eqTrans
    (GaussianNameArithmetic.recode_congr (qadd_congr (GaussianGammaCanonicalExponent.product_sample_at _ z B N)
      (GaussianGammaCanonicalTailName.point_at _ z R B N)))
theorem exponent_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN exponentF (exponentData z R B N) :=
  GaussianNameArithmetic.add_fast productF GaussianGammaCanonicalTailName.pointF _ _
    (product_regular z B N) (GaussianGammaCanonicalTailName.name_regular z R B N h)
theorem exponent_sample_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (exponentPoint p z R B N) (exponentRadius z R B N) one :=
  GaussianNameBounds.sample_bound exponentF _ p (exponent_regular z R B N h)
theorem exponential_input (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input exponentF (exponentRadius z R B N) (exponentData z R B N) := by
  have cn := exponent_regular z R B N h
  refine .andI cn ?_
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianRootApproximationWitness.pointBounds,exponentRadius] using
    GaussianNameBounds.all_samples_bounded exponentF (exponentData z R B N) cn
theorem exponential_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN exponentialF (exponentialData z R B N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input z R B N h)
theorem exponential_sample_at (p z R B N : PTm n) : Γ ⊢[PRAAx] exponentialPoint p z R B N ≐
    GaussianRationalPolynomialExponential.scalarSum
      (exponentPoint (GaussianRadiusExponentialName.inputPrecision (exponentRadius z R B N) p) z R B N)
      (GaussianRadiusExponentialName.index (exponentRadius z R B N) p) :=
  GaussianRadiusExponentialName.sample_at exponentF _ p _
theorem sample_at (p z R B N : PTm n) : Γ ⊢[PRAAx] sample p z R B N ≐ value p z R B N :=
  (GaussianNameArithmetic.multiply_at constantF exponentialF (head z B N) (exponentialData z R B N) p).eqTrans
    (GaussianNameArithmetic.recode_congr (qmul_congr (constant_at _ _) (.eqRefl _)))
theorem name_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B N) :=
  GaussianNameArithmetic.multiply_fast constantF exponentialF _ _ (constant_regular _) (exponential_regular z R B N h)
theorem head_bound (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (head z B N) (R*pw (one+R) N) one :=
  GaussianGammaEulerHead.returned_head_bound _ _ _ _ h.andE₁ h.andE₂.andE₂.andE₁
theorem sample_bound (p z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B N) :
    Γ ⊢[PRAAx] bounded (sample p z R B N) (diskBound z R B N) one :=
  GaussianNameBounds.sample_bound nameF _ p (name_regular z R B N h)

/-- Literal agreement with the original frozen C7 construction. -/
theorem original_exponent_data (z R B : PTm n) : Γ ⊢[PRAAx]
    exponentData z R B (two*R) ≐ GaussianGammaCanonicalExponent.exponentData z R B := .eqRefl _
theorem original_exponential_data (z R B : PTm n) : Γ ⊢[PRAAx]
    exponentialData z R B (two*R) ≐ GaussianGammaCanonicalExponent.exponentialData z R B := .eqRefl _
theorem original_C7_data (z R B : PTm n) : Γ ⊢[PRAAx]
    data z R B (two*R) ≐ GaussianGammaC7Name.data z R B := .eqRefl _
theorem original_C7_sample (p z R B : PTm n) : Γ ⊢[PRAAx]
    sample p z R B (two*R) ≐ GaussianGammaC7Name.sample p z R B := .eqRefl _

theorem actual_cutoff_exponent_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (exponentPoint (var 0) (var 1) (var 2) (var 3) (var 4) ≐ exponentValue (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (exponent_sample_at _ _ _ _ _)
theorem original_cutoff_exponent_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN exponentF (exponentData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (exponent_regular _ _ _ _ Prf.hyp0))
theorem original_cutoff_exponential_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN exponentialF (exponentialData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (exponential_regular _ _ _ _ Prf.hyp0))
theorem original_cutoff_C7_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (name_regular _ _ _ _ Prf.hyp0))
theorem actual_cutoff_C7_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) ≐ value (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (sample_at _ _ _ _ _)
theorem original_cutoff_head_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ bounded (head (var 0) (var 2) (var 3))
      (var 1*pw (one+var 1) (var 3)) one) := closeUniv 4 (.impI (head_bound _ _ _ _ Prf.hyp0))
theorem original_cutoff_C7_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶ bounded (sample (var 0) (var 1) (var 2) (var 3) (var 4))
      (diskBound (var 1) (var 2) (var 3) (var 4)) one) := closeUniv 5 (.impI (sample_bound _ _ _ _ _ Prf.hyp0))
theorem actual_original_C7_specialization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (sample (var 0) (var 1) (var 2) (var 3) (two*var 2) ≐ GaussianGammaC7Name.sample (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (original_C7_sample _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaCutoffName
