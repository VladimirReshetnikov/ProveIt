import OAI.Combinatorics.Progressions.Fourier.AllocatedSiteSpectrumBudget
import OAI.Combinatorics.Progressions.Linear.AllocatedAveragedCoarseKernelComparison
import OAI.Combinatorics.Progressions.Polynomial.AllocatedIdealScalePolynomial

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def siteSpectrumBlockCount (m : ℕ) : ℕ :=
  1 + ∑ j : Fin m, ∑ k : Fin (2 ^ (m + 1) + 1),
    positiveModerateSpectrumBlockCount j.val k.val ((layerTailDegree m + 2) * k.val)

theorem siteSpectrumBlockCount_pos (m : ℕ) : 0 < siteSpectrumBlockCount m := by
  unfold siteSpectrumBlockCount
  omega

theorem siteSpectrumBlockCount_bound (m : ℕ) (j : Fin m) (k : ℕ) (hk : k ≤ 2 ^ (m + 1)) :
    positiveModerateSpectrumBlockCount j.val k ((layerTailDegree m + 2) * k) ≤
      siteSpectrumBlockCount m := by
  have hi := Finset.single_le_sum
    (fun (k : Fin (2 ^ (m + 1) + 1)) _ => Nat.zero_le
      (positiveModerateSpectrumBlockCount j.val k.val ((layerTailDegree m + 2) * k.val)))
    (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (2 ^ (m + 1) + 1)))
  have ho := Finset.single_le_sum
    (fun (j : Fin m) _ => Nat.zero_le
      (∑ k : Fin (2 ^ (m + 1) + 1), positiveModerateSpectrumBlockCount j.val k.val
        ((layerTailDegree m + 2) * k.val))) (Finset.mem_univ j)
  exact (hi.trans ho).trans (Nat.le_add_left _ 1)

theorem principalProfileSize_le_radius {R : ℝ} (hR : 0 ≤ R) (b : ℕ) :
    principalProfileSize R b ≤ R := by
  unfold principalProfileSize
  exact div_le_self hR (by have hb := Nat.cast_nonneg (α := ℝ) b; linarith)

theorem principalProfileSize_le_natScale {R : ℝ} (hR : 0 ≤ R) (hR1 : R ≤ 1)
    (b S : ℕ) (hS : 0 < S) : principalProfileSize R b ≤ S :=
  (principalProfileSize_le_radius hR b).trans (hR1.trans (by exact_mod_cast hS))

namespace VectorPolynomial

theorem allocatedUniformBlocks_spectrum_bound {m : ℕ} {I : Fin m → Type*} {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
    (hq : Fintype.card α ≤ m + 1)
    (hB : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (a : Σ j : Fin m, Fin (n j)) :
    positiveModerateSpectrumBlockCount a.1.val (rowSets a.1).card
        ((layerTailDegree m + 2) * (rowSets a.1).card) ≤ Fintype.card (B ⟨a.1, Sum.inr a.2⟩) :=
  (siteSpectrumBlockCount_bound m a.1 (rowSets a.1).card (finiteBooleanRows_card_le _ hq)).trans (hB a.1 a.2)

noncomputable def allocatedPositiveSitePeriod {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (α : Type*) [Fintype α] {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
    (S : LayerSamplerScale (G := G) B U b R σ)
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) : ℕ+ :=
  ⟨allocatedGridTorusFactor B α (allocatedGridIntegerAxis B U b S a) *
      allocatedGridNaturalScale B U b S a,
    Nat.mul_pos (blockTorusFactor_pos _ _ _ _)
      (allocatedGridNaturalScale_pos B U b hR S a)⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

def allocatedSiteKernelMaskLog {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  (m * 2 ^ (m + 1) : ℕ) * p

def allocatedSiteScaleNumeric {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  (m + 2 : ℕ) * (p + 1) + p

noncomputable def allocatedSiteScaleLog {A : Type*} [Semiring A]
    (m : ℕ) (p e E : A) : A :=
  allocatedIdealScaleLog m (allocatedComparisonDimension m p)
    (allocatedSiteScaleNumeric m p) e (allocatedSiteKernelMaskLog m p) E

noncomputable def allocatedSiteSourceLog {A : Type*} [Semiring A]
    (m : ℕ) (p e E : A) : A :=
  canonicalScalarSourceLog m p + allocatedSiteScaleLog m p e E + p + e + E + 4

theorem allocatedSiteKernelMaskLog_nonneg (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedSiteKernelMaskLog m p := mul_nonneg (Nat.cast_nonneg _) hp

theorem allocatedSiteScaleNumeric_bounds (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedSiteScaleNumeric m p ∧ p ≤ allocatedSiteScaleNumeric m p ∧
      (m + 1 : ℕ) * p + (m + 2 : ℕ) ≤ allocatedSiteScaleNumeric m p := by
  unfold allocatedSiteScaleNumeric
  push_cast
  have hm := Nat.cast_nonneg (α := ℝ) m
  constructor
  · positivity
  constructor <;> nlinarith

theorem allocatedSiteSourceLog_bounds (m : ℕ) {p e E : ℝ}
    (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E) :
    0 ≤ allocatedSiteScaleLog m p e E ∧ 0 ≤ allocatedSiteSourceLog m p e E ∧
      p ≤ allocatedSiteSourceLog m p e E ∧ E + 4 ≤ allocatedSiteSourceLog m p e E ∧
      canonicalScalarSourceLog m p ≤ allocatedSiteSourceLog m p e E ∧
      allocatedSiteScaleLog m p e E ≤ allocatedSiteSourceLog m p e E := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hN := (allocatedSiteScaleNumeric_bounds m hp).1
  have hw := allocatedSiteKernelMaskLog_nonneg m hp
  obtain ⟨_, hQ, _, _, _, hQL⟩ := allocatedIdealScaleInput_bounds m hD hN he hw hE
  have hL : 0 ≤ allocatedSiteScaleLog m p e E := hQ.trans hQL
  have hC := (canonicalScalarSourceLog_bounds m hp).1
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_⟩
  all_goals unfold allocatedSiteSourceLog; linarith

theorem exists_allocatedSiteSourceLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → allocatedSiteSourceLog m p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedSiteSourceLog m Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedSiteSourceLog, allocatedSiteScaleLog, allocatedSiteScaleNumeric,
    allocatedSiteKernelMaskLog, canonicalScalarSourceLog, allocatedComparisonDimension,
    allocatedIdealScaleLog, allocatedIdealScaleInput, allocatedPhysicalIdealLengthEnvelope,
    allocatedTestLengthEnvelope, allocatedJointLengthEnvelope, allocatedTestEnvelope,
    allocatedFrontEnvelope, allocatedAccuracyEnvelope, allocatedTupleEnvelope,
    allocatedKernelEnvelope, allocatedIdealMeshEnvelope, allocatedIdealGridEnvelope,
    allocatedIdealRadiusEnvelope, allocatedProxyLipEnvelope, allocatedIdealLipEnvelope,
    allocatedSupportEnvelope, allocatedDensityEnvelope, kernelOutputEnvelope,
    kernelGeometryEnvelope, kernelInverseEnvelope, Polynomial.eval₂_pow] using hbound p hp

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedSiteScale (p e E : ℝ) : LayerSamplerScale (G := G) B U b R σ :=
  allocatedIdealScale (G := G) B U b hR hσ (allocatedComparisonDimension m p)
    (allocatedSiteScaleNumeric m p) e (allocatedSiteKernelMaskLog m p) E

theorem allocatedSiteScale_lower {p e E : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E) :
    Real.exp (allocatedSiteScaleNumeric m p) ≤ (allocatedSiteScale (G := G) B U b hR hσ p e E).value :=
  allocatedIdealScale_ge_exp (G := G) B U b hR hσ (allocatedComparisonDimension_bounds m hp).1
    (allocatedSiteScaleNumeric_bounds m hp).1 he (allocatedSiteKernelMaskLog_nonneg m hp) hE

theorem allocatedSiteScale_period_window {dim M : ℕ} {p e E : ℝ}
    (hdim : dim ≤ m + 1) (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hM : (M : ℝ) ≤ Real.exp p) :
    (Fintype.card (Fin dim) + 1) * M ^ (m + 1) ≤ (allocatedSiteScale (G := G) B U b hR hσ p e E).value := by
  have hdim' : ((dim + 1 : ℕ) : ℝ) ≤ Real.exp (m + 2 : ℕ) := by
    have hd : ((dim + 1 : ℕ) : ℝ) ≤ (m + 2 : ℕ) := by exact_mod_cast (show dim + 1 ≤ m + 2 by omega)
    exact hd.trans (by linarith [Real.add_one_le_exp ((m + 2 : ℕ) : ℝ)])
  have hpow := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg M) hM hp (m + 1) le_rfl
  have hprod := (mul_le_mul hdim' hpow (pow_nonneg (Nat.cast_nonneg M) _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hnum := (allocatedSiteScaleNumeric_bounds m hp).2.2
  have hout := hprod.trans ((Real.exp_le_exp.mpr
    (by simpa only [add_comm] using hnum)).trans (allocatedSiteScale_lower (G := G) B U b hR hσ hp he hE))
  simpa only [Fintype.card_fin] using (show (dim + 1) * M ^ (m + 1) ≤
    (allocatedSiteScale (G := G) B U b hR hσ p e E).value by exact_mod_cast hout)

variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedSiteScale_upper
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    {p e E : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p) :
    ((allocatedSiteScale (G := G) B U b hR hσ p e E).value : ℝ) ≤ Real.exp (allocatedSiteScaleLog m p e E) := by
  have hd := allocatedComparisonDimensions_of_primitive B rows hq hinj hp hvars hI hn
  have hN := allocatedSiteScaleNumeric_bounds m hp
  exact allocatedIdealScale_upper (G := G) B U b hR hσ hd hN.1 he
    (allocatedSiteKernelMaskLog_nonneg m hp) hE
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hN.2.1))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hN.2.1))

theorem allocatedSiteScale_ready
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    {p e E : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    let D := allocatedComparisonDimension m p
    let q := allocatedSiteScaleNumeric m p
    let w := allocatedSiteKernelMaskLog m p
    let S := allocatedSiteScale (G := G) B U b hR hσ p e E
    Real.exp (allocatedJointLengthLog (G := G) B α O q
        (E + allocatedIdealVolumeEnvelope m D q + 3)) ≤ S.value ∧
      1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤
        physicalIdealErrorShare E (D * w + allocatedIdealMeshEnvelope m D q e) := by
  have hd := allocatedComparisonDimensions_of_primitive B rows hq hinj hp hvars hI hn
  exact allocatedIdealScale_ready (G := G) B U b hR hσ hd (allocatedSiteScaleNumeric_bounds m hp).1
    he (allocatedSiteKernelMaskLog_nonneg m hp) hE

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem boundedCoefficientExponent_card_add_one_le_site_numeric
    {K : Type*} [Fintype K] {m h : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hK : (Fintype.card K : ℝ) ≤ p) (hh : h ≤ m) :
    (Fintype.card (BoundedCoefficientExponent K h) : ℝ) + 1 ≤
      Real.exp (allocatedSiteScaleNumeric m p) := by
  have hbase : (Fintype.card K : ℝ) + 1 ≤ Real.exp p := by
    linarith [Real.add_one_le_exp p]
  have hfactor : ((h + 1 : ℕ) : ℝ) ≤ Real.exp (m + 1 : ℕ) := by
    have hm : ((h + 1 : ℕ) : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.add_le_add_right hh 1
    exact hm.trans (by linarith [Real.add_one_le_exp ((m + 1 : ℕ) : ℝ)])
  have hpow : ((Fintype.card K : ℝ) + 1) ^ h ≤ Real.exp ((m : ℝ) * p) :=
    pow_le_exp_mul_of_le_exp (by positivity) hbase hp h (Nat.cast_le.mpr hh)
  have hcount : (Fintype.card (BoundedCoefficientExponent K h) : ℝ) ≤
      Real.exp (((m + 1 : ℕ) : ℝ) + (m : ℝ) * p) := by
    have hc : (Fintype.card (BoundedCoefficientExponent K h) : ℝ) ≤
        ((h + 1 : ℕ) : ℝ) * ((Fintype.card K : ℝ) + 1) ^ h := by
      exact_mod_cast boundedCoefficientExponent_card_le (K := K) h
    exact hc.trans ((mul_le_mul hfactor hpow (by positivity) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm)
  have hlog : 0 ≤ ((m + 1 : ℕ) : ℝ) + (m : ℝ) * p := by positivity
  have hnumeric : ((m + 1 : ℕ) : ℝ) + (m : ℝ) * p + 1 ≤ allocatedSiteScaleNumeric m p := by
    unfold allocatedSiteScaleNumeric
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hout := (one_add_le_exp_succ hlog hcount).trans (Real.exp_le_exp.mpr hnumeric)
  simpa only [add_comm] using hout

theorem allocatedSiteScale_coefficient_count
    {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {p : ℝ} (hp : 0 ≤ p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p) :
    ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤
        Real.exp (allocatedSiteScaleNumeric m p) :=
  fun j => boundedCoefficientExponent_card_add_one_le_site_numeric hp hvars (Nat.succ_le_of_lt j.isLt)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

def canonicalSiteBlockCount (m : ℕ) : ℕ := siteSpectrumBlockCount m + 2 ^ (m + 1)

theorem canonicalSiteBlockCount_pos (m : ℕ) : 0 < canonicalSiteBlockCount m := by
  unfold canonicalSiteBlockCount
  exact lt_of_lt_of_le (siteSpectrumBlockCount_pos m) (Nat.le_add_right _ _)

instance canonicalSiteBlockCount_neZero (m : ℕ) : NeZero (canonicalSiteBlockCount m) :=
  ⟨(canonicalSiteBlockCount_pos m).ne'⟩

abbrev canonicalSiteBlocks {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ)
    (_ : LayerSamplerAxis I n) : Type := Fin (canonicalSiteBlockCount m)

theorem canonicalSiteBlocks_spectrum_count {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ)
    (j : Fin m) (i : Fin (n j)) :
    siteSpectrumBlockCount m ≤ Fintype.card (canonicalSiteBlocks I n ⟨j, Sum.inr i⟩) := by
  rw [Fintype.card_eq_nat_card]
  change siteSpectrumBlockCount m ≤ Nat.card (Fin (canonicalSiteBlockCount m))
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact Nat.le_add_right _ _

theorem canonicalSiteBlockCount_jet_bound {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α ≤ m + 1) (h : ℕ) :
    Fintype.card (BoundedBooleanJet α h) ≤ canonicalSiteBlockCount m := by
  have hcard : Fintype.card (BoundedBooleanJet α h) ≤ 2 ^ Fintype.card α := by
    simpa using Fintype.card_le_of_injective
      (fun r : BoundedBooleanJet α h => r.val) Subtype.val_injective
  have hp := Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hα
  unfold canonicalSiteBlockCount
  omega

noncomputable def canonicalSiteBlockEmbedding {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (hα : Fintype.card α ≤ m + 1) (h : ℕ) :
    BoundedBooleanJet α h ↪ Fin (canonicalSiteBlockCount m) := by
  let e := Fintype.equivFin (BoundedBooleanJet α h)
  refine ⟨fun x => ⟨(e x).val, lt_of_lt_of_le (e x).isLt (canonicalSiteBlockCount_jet_bound hα h)⟩, ?_⟩
  intro x y hxy
  apply e.injective
  exact Fin.ext (congrArg (fun z : Fin (canonicalSiteBlockCount m) => z.val) hxy)

noncomputable def canonicalSiteBlocks_jetEmbedding {m : ℕ} (I : Fin m → Type*) (n : Fin m → ℕ)
    {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α ≤ m + 1)
    (a : LayerSamplerAxis I n) :
    BoundedBooleanJet α (a.1.val + 1) ↪ canonicalSiteBlocks I n a :=
  canonicalSiteBlockEmbedding hα (a.1.val + 1)

def canonicalSiteVariableFactor (m : ℕ) : ℕ := 1 + canonicalSiteBlockCount m * (2 * m) * m

theorem canonicalSiteBlocks_variables_card {m : ℕ} (G : Type*) [Fintype G]
    (I : Fin m → Type*) [∀ j, Fintype (I j)] (n : Fin m → ℕ) :
    Fintype.card (LayerSamplerVariables G I n (canonicalSiteBlocks I n)) =
      Fintype.card G + canonicalSiteBlockCount m * ∑ a : LayerSamplerAxis I n, layerSamplerDegree I n a := by
  simp only [LayerSamplerVariables, samplerTupleIndex_card, canonicalSiteBlocks, Fintype.card_fin,
    Finset.mul_sum]

theorem canonicalSiteBlocks_variables_bound {m : ℕ} (G : Type*) [Fintype G]
    (I : Fin m → Type*) [∀ j, Fintype (I j)] (n : Fin m → ℕ)
    {p : ℝ} (hG : (Fintype.card G : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    (Fintype.card (LayerSamplerVariables G I n (canonicalSiteBlocks I n)) : ℝ) ≤
      canonicalSiteVariableFactor m * p := by
  have haxes := allocatedAxes_card_le (I := I) (n := n) hI hn
  have hdegree : ((∑ a : LayerSamplerAxis I n, layerSamplerDegree I n a : ℕ) : ℝ) ≤
      (Fintype.card (LayerSamplerAxis I n) : ℝ) * m := by
    rw [Nat.cast_sum]
    calc
      _ ≤ ∑ _a : LayerSamplerAxis I n, (m : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        exact Nat.cast_le.mpr (Nat.succ_le_of_lt a.1.isLt)
      _ = _ := by simp
  rw [canonicalSiteBlocks_variables_card, Nat.cast_add, Nat.cast_mul]
  calc
    _ ≤ p + (canonicalSiteBlockCount m : ℝ) * ((Fintype.card (LayerSamplerAxis I n) : ℝ) * m) :=
      add_le_add hG (mul_le_mul_of_nonneg_left hdegree (Nat.cast_nonneg _))
    _ ≤ p + (canonicalSiteBlockCount m : ℝ) * (((2 * m : ℕ) : ℝ) * p * m) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right haxes (Nat.cast_nonneg m)) (Nat.cast_nonneg _))
    _ = _ := by unfold canonicalSiteVariableFactor; push_cast; ring

theorem canonicalSiteBlocks_coefficient_count {m : ℕ} (G : Type*) [Fintype G]
    (I : Fin m → Type*) [∀ j, Fintype (I j)] (n : Fin m → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hG : (Fintype.card G : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    ∀ j : Fin m, (Fintype.card
      (BoundedCoefficientExponent (LayerSamplerVariables G I n (canonicalSiteBlocks I n))
        (j.val + 1)) : ℝ) + 1 ≤
          Real.exp (allocatedSiteScaleNumeric m (canonicalSiteVariableFactor m * p)) :=
  allocatedSiteScale_coefficient_count (canonicalSiteBlocks I n)
    (mul_nonneg (Nat.cast_nonneg _) hp) (canonicalSiteBlocks_variables_bound G I n hG hI hn)

end Erdos3.VectorPolynomial

end

end OAI
