import IPRADerivations.Analysis.Names.RationalGaussianNameEmbedding
import IPRADerivations.Analysis.Gamma.EulerProducts.GammaEulerConstantName
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaCanonicalTailName
import IPRADerivations.Analysis.Names.GaussianNameArithmetic

/-!
# The actual Gamma C7 exponent at K=2R

Original harmonic-mesh Euler observations, the exact factorial-denominator
H_K, constant z/B and the ORIGINAL canonical tail T_K are combined by the
checked Gaussian name operations. The literal samples retain their actual
computed precision shifts and normalizations. Original disk inputs derive
regularity; the actual zeroth sample computes a genuine integer disk for
the verified larger-disk exponential. No output name/size law is supplied.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalExponent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (ofGaussian qadd qmul positive_product)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def harmonic (K : PTm n) : PTm n := RationalIntegerNormalization.normalize
  (ZT.ofNat (AnalyticNumberTheory.Harmonic.S K (Products.fact K))) (Products.fact K)
def harmonicPoint (K : PTm n) : PTm n := RationalGaussianEmbedding.embed (harmonic K)
def gammaF : PR 2 := RationalGaussianNameEmbedding.nameF GammaEulerConstantName.gammaF
/-- The constant name preserves the supplied actual point code. -/
def constantF : PR 2 := PTm.toPR (var 1 : PTm 2)
def differenceF : PR 2 := GaussianNameArithmetic.addF gammaF constantF
def differenceData (K : PTm n) : PTm n := GaussianNameArithmetic.addData zero (qnegative (harmonicPoint K))
def productF : PR 2 := GaussianNameArithmetic.multiplyF differenceF constantF
def productData (z B K : PTm n) : PTm n := GaussianNameArithmetic.multiplyData differenceF constantF
  (differenceData K) (ofGaussian z B)
def exponentF : PR 2 := GaussianNameArithmetic.addF productF GaussianGammaCanonicalTailName.pointF
def exponentData (z R B : PTm n) : PTm n := GaussianNameArithmetic.addData
  (productData z B (two*R)) (GaussianGammaCanonicalTailName.data z R B (two*R))
def exponentPoint (p z R B : PTm n) : PTm n := ap2 exponentF p (exponentData z R B)
def source (z R B : PTm n) : Fm PTm n := le one R ⋏ (le one B ⋏ ComplexLogarithmRemainder.bounded z (R*B))
@[simp] theorem subst_harmonic {l : ℕ} (σ : Fin n → PTm l) (K : PTm n) :
    Syn.subst σ (harmonic K) = harmonic (Syn.subst σ K) := by simp [harmonic,AnalyticNumberTheory.Harmonic.S,Products.fact]
@[simp] theorem subst_harmonicPoint {l : ℕ} (σ : Fin n → PTm l) (K : PTm n) :
    Syn.subst σ (harmonicPoint K) = harmonicPoint (Syn.subst σ K) := by simp [harmonicPoint]
@[simp] theorem subst_differenceData {l : ℕ} (σ : Fin n → PTm l) (K : PTm n) :
    Syn.subst σ (differenceData K) = differenceData (Syn.subst σ K) := by simp [differenceData]
@[simp] theorem subst_productData {l : ℕ} (σ : Fin n → PTm l) (z B K : PTm n) :
    Syn.subst σ (productData z B K) = productData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ K) := by simp [productData]
@[simp] theorem subst_exponentData {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (exponentData z R B) = exponentData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [exponentData]
@[simp] theorem subst_exponentPoint {l : ℕ} (σ : Fin n → PTm l) (p z R B : PTm n) :
    Syn.subst σ (exponentPoint p z R B) = exponentPoint (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [exponentPoint]
@[simp] theorem subst_source {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    (source z R B).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [source]

theorem harmonic_represents (K : PTm n) : Γ ⊢[PRAAx] RationalArithmetic.represents (harmonic K)
    (ZT.ofNat (AnalyticNumberTheory.Harmonic.S K (Products.fact K))) (Products.fact K) :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (GammaEulerMesh.factorial_positive K)
theorem harmonic_canonical (K : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (harmonic K) :=
  RationalNormalForm.normalize_well_formed _ _ (GammaEulerMesh.factorial_positive K)
theorem gamma_sample_at (p : PTm n) : Γ ⊢[PRAAx] ap2 gammaF p zero ≐
    RationalGaussianEmbedding.embed (GammaEulerConstantName.gammaSample p zero) :=
  RationalGaussianNameEmbedding.sample_at GammaEulerConstantName.gammaF p zero
theorem gamma_regular : Γ ⊢[PRAAx] pointCN gammaF (zero : PTm n) :=
  RationalGaussianNameEmbedding.name_regular GammaEulerConstantName.gammaF zero (GammaEulerConstantName.gamma_name_regular zero)
theorem constant_at (p q : PTm n) : Γ ⊢[PRAAx] ap2 constantF p q ≐ q := by
  simpa [constantF,ap2] using toPR_eq (Γ := Γ) (var 1 : PTm 2) ![p,q]
theorem constant_regularity (q s t : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 constantF s q) (ap2 constantF t q) (unit s+unit t) (unit s*unit t) :=
  GaussianRationalDistanceOrder.distance_congr (constant_at s q).eqSymm (constant_at t q).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
      (positive_product _ _ (unit_positive s) (unit_positive t)) (positive_product _ _ (unit_positive s) (unit_positive t))
      (le_of_eq_add (d := (unit s+unit t)*(unit s*unit t)) (by ipra_ring))
      (GaussianRationalPowerDifference.distance_refl_zero q (unit s*unit t) (positive_product _ _ (unit_positive s) (unit_positive t))))
theorem constant_regular (q : PTm n) : Γ ⊢[PRAAx] pointCN constantF q := by
  refine .allI (.allI ?_)
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,Syn.shift] using
    constant_regularity (Γ := (Γ.map Fm.shift).map Fm.shift) (Syn.shift (Syn.shift q)) (var 1) (var 0)

/-! Literal scheduled samples, including every actual normalization. -/
def addPrecision (p : PTm n) : PTm n := GaussianFastValueCut.exponent two p
def productPrecision (z B K p : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus differenceF constantF (differenceData K) (ofGaussian z B)) p
def differenceValue (p K : PTm n) : PTm n := GaussianFastValueCut.recode
  (qsub (RationalGaussianEmbedding.embed (GammaEulerConstantName.gammaSample (addPrecision p) zero)) (harmonicPoint K))
def productValue (p z B K : PTm n) : PTm n := GaussianFastValueCut.recode
  (qmul (differenceValue (productPrecision z B K p) K) (ofGaussian z B))
def exponentValue (p z R B : PTm n) : PTm n := GaussianFastValueCut.recode
  (qadd (productValue (addPrecision p) z B (two*R))
    (GaussianGammaCanonicalTailName.value (addPrecision p) z R B (two*R)))
@[simp] theorem subst_addPrecision {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) :
    Syn.subst σ (addPrecision p) = addPrecision (Syn.subst σ p) := by simp [addPrecision]
@[simp] theorem subst_productPrecision {l : ℕ} (σ : Fin n → PTm l) (z B K p : PTm n) :
    Syn.subst σ (productPrecision z B K p) = productPrecision (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ K) (Syn.subst σ p) := by simp [productPrecision]
@[simp] theorem subst_differenceValue {l : ℕ} (σ : Fin n → PTm l) (p K : PTm n) :
    Syn.subst σ (differenceValue p K) = differenceValue (Syn.subst σ p) (Syn.subst σ K) := by simp [differenceValue]
@[simp] theorem subst_productValue {l : ℕ} (σ : Fin n → PTm l) (p z B K : PTm n) :
    Syn.subst σ (productValue p z B K) = productValue (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ K) := by simp [productValue]
@[simp] theorem subst_exponentValue {l : ℕ} (σ : Fin n → PTm l) (p z R B : PTm n) :
    Syn.subst σ (exponentValue p z R B) = exponentValue (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [exponentValue]

theorem difference_sample_at (p K : PTm n) : Γ ⊢[PRAAx] ap2 differenceF p (differenceData K) ≐ differenceValue p K :=
  (GaussianNameArithmetic.add_at gammaF constantF zero (qnegative (harmonicPoint K)) p).eqTrans
    (GaussianNameArithmetic.recode_congr (qadd_congr (gamma_sample_at _) (constant_at _ _)))
theorem product_sample_at (p z B K : PTm n) : Γ ⊢[PRAAx] ap2 productF p (productData z B K) ≐ productValue p z B K :=
  (GaussianNameArithmetic.multiply_at differenceF constantF (differenceData K) (ofGaussian z B) p).eqTrans
    (GaussianNameArithmetic.recode_congr (qmul_congr (difference_sample_at _ K) (constant_at _ _)))
theorem exponent_sample_at (p z R B : PTm n) : Γ ⊢[PRAAx] exponentPoint p z R B ≐ exponentValue p z R B :=
  (GaussianNameArithmetic.add_at productF GaussianGammaCanonicalTailName.pointF
    (productData z B (two*R)) (GaussianGammaCanonicalTailName.data z R B (two*R)) p).eqTrans
      (GaussianNameArithmetic.recode_congr (qadd_congr (product_sample_at _ z B (two*R))
        (GaussianGammaCanonicalTailName.point_at _ z R B (two*R))))

theorem tail_source (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalTailName.source z R B (two*R) :=
  .andI h.andE₂.andE₁ (.andI (le_trans h.andE₁ (le_of_eq_add (d := R) (by ipra_ring)))
    (.andI h.andE₂.andE₂ (le_refl _)))
theorem difference_regular (K : PTm n) : Γ ⊢[PRAAx] pointCN differenceF (differenceData K) :=
  GaussianNameArithmetic.add_fast gammaF constantF zero (qnegative (harmonicPoint K)) gamma_regular (constant_regular _)
theorem product_regular (z B K : PTm n) : Γ ⊢[PRAAx] pointCN productF (productData z B K) :=
  GaussianNameArithmetic.multiply_fast differenceF constantF (differenceData K) (ofGaussian z B)
    (difference_regular K) (constant_regular _)
theorem exponent_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    pointCN exponentF (exponentData z R B) :=
  GaussianNameArithmetic.add_fast productF GaussianGammaCanonicalTailName.pointF (productData z B (two*R))
    (GaussianGammaCanonicalTailName.data z R B (two*R)) (product_regular z B (two*R))
    (GaussianGammaCanonicalTailName.name_regular z R B (two*R) (tail_source z R B h))

def exponentRadius (z R B : PTm n) : PTm n := GaussianNameBounds.U exponentF (exponentData z R B)
def exponentialF : PR 2 := GaussianRadiusExponentialName.nameF exponentF
def exponentialData (z R B : PTm n) : PTm n := GaussianRadiusExponentialName.data (exponentRadius z R B) (exponentData z R B)
def exponentialPoint (p z R B : PTm n) : PTm n := ap2 exponentialF p (exponentialData z R B)
@[simp] theorem subst_exponentRadius {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (exponentRadius z R B) = exponentRadius (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [exponentRadius]
@[simp] theorem subst_exponentialData {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (exponentialData z R B) = exponentialData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [exponentialData]
@[simp] theorem subst_exponentialPoint {l : ℕ} (σ : Fin n → PTm l) (p z R B : PTm n) :
    Syn.subst σ (exponentialPoint p z R B) = exponentialPoint (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [exponentialPoint]

theorem exponent_sample_bound (p z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (exponentPoint p z R B) (exponentRadius z R B) one :=
  GaussianNameBounds.sample_bound exponentF (exponentData z R B) p (exponent_regular z R B h)
theorem exponential_input (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input exponentF (exponentRadius z R B) (exponentData z R B) := by
  have cn := exponent_regular z R B h
  refine .andI cn ?_
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianRootApproximationWitness.pointBounds,exponentRadius] using
    GaussianNameBounds.all_samples_bounded exponentF (exponentData z R B) cn
theorem exponential_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    pointCN exponentialF (exponentialData z R B) := GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input z R B h)
theorem exponential_sample_at (p z R B : PTm n) : Γ ⊢[PRAAx] exponentialPoint p z R B ≐
    GaussianRationalPolynomialExponential.scalarSum
      (exponentPoint (GaussianRadiusExponentialName.inputPrecision (exponentRadius z R B) p) z R B)
      (GaussianRadiusExponentialName.index (exponentRadius z R B) p) :=
  GaussianRadiusExponentialName.sample_at exponentF (exponentRadius z R B) p (exponentData z R B)

/-! Actual PR3 preparation data for the source C7 exponential factor. -/
def output (z R B : PTm n) : PTm n := pairT (exponentData z R B)
  (pairT (exponentialData z R B) (pairT (two*R) (exponentRadius z R B)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (z R B : PTm n) : PTm n := ap3 outputF z R B
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (output z R B) = output (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (run z R B) = run (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [run]
theorem program_at (z R B : PTm n) : Γ ⊢[PRAAx] run z R B ≐ output z R B := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![z,R,B]
theorem returned_exponent_data (z R B : PTm n) : Γ ⊢[PRAAx] fstT (run z R B) ≐ exponentData z R B :=
  (congrFst (program_at _ _ _)).eqTrans (fst_pair _ _)
theorem returned_exponential_data (z R B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run z R B)) ≐ exponentialData z R B :=
  (congrFst ((congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_parameters (z R B : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run z R B)) ≐ pairT (two*R) (exponentRadius z R B) :=
  (congrSnd ((congrSnd (program_at _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem actual_original_harmonic_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (RationalArithmetic.represents (harmonic (var 0))
      (ZT.ofNat (AnalyticNumberTheory.Harmonic.S (var 0) (Products.fact (var 0)))) (Products.fact (var 0))) :=
  closeUniv 1 (harmonic_represents _)
theorem actual_embedded_euler_gamma_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN gammaF zero ⋏ ap2 gammaF (var 0) zero ≐ RationalGaussianEmbedding.embed (GammaEulerConstantName.gammaSample (var 0) zero)) :=
  closeUniv 1 (.andI gamma_regular (gamma_sample_at _))
theorem actual_gamma_C7_exponent_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (exponentPoint (var 0) (var 1) (var 2) (var 3) ≐ exponentValue (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (exponent_sample_at _ _ _ _)
theorem original_gamma_C7_exponent_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ pointCN exponentF (exponentData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (exponent_regular _ _ _ Prf.hyp0))
theorem original_gamma_C7_exponent_sample_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ GaussianRationalMetric.bounded
      (exponentPoint (var 0) (var 1) (var 2) (var 3)) (exponentRadius (var 1) (var 2) (var 3)) one) :=
  closeUniv 4 (.impI (exponent_sample_bound _ _ _ _ Prf.hyp0))
theorem original_gamma_C7_exponential_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ pointCN exponentialF (exponentialData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (exponential_regular _ _ _ Prf.hyp0))
theorem actual_gamma_C7_exponential_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (exponentialPoint (var 0) (var 1) (var 2) (var 3) ≐ GaussianRationalPolynomialExponential.scalarSum
      (exponentPoint (GaussianRadiusExponentialName.inputPrecision (exponentRadius (var 1) (var 2) (var 3)) (var 0)) (var 1) (var 2) (var 3))
      (GaussianRadiusExponentialName.index (exponentRadius (var 1) (var 2) (var 3)) (var 0))) :=
  closeUniv 4 (exponential_sample_at _ _ _ _)
theorem actual_gamma_C7_preparation_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_gamma_C7_exponential_data_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (fstT (sndT (run (var 0) (var 1) (var 2))) ≐ exponentialData (var 0) (var 1) (var 2)) :=
  closeUniv 3 (returned_exponential_data _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalExponent
