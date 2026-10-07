/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.AllocatedProxyL1Averaging
import OAI.Combinatorics.Progressions.Geometry.AllocatedProxyOutputSupport
import OAI.Combinatorics.Progressions.Lattices.AllocatedLongLatticeScale
import OAI.Combinatorics.Progressions.Probability.SelectedDependentMeasure

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "select" => allocatedLongIntegerSelect B U basis S (O := O)
local notation "realOutput" => UnselectedColumn select
local notation "scalar" => fun q : output => CoefficientJetScalar (Subtype.val (Sigma.fst q))

noncomputable def allocatedLongScalarEquiv :
    AllocatedLongJetRows B U basis S O ≃ᵐ (∀ q : output, scalar q) :=
  (MeasurableEquiv.piCongrRight (fun a : {a // ¬grid a} =>
    coefficientJetScalarEquiv O a.val)).trans
    (MeasurableEquiv.piCurry (fun (a : {a // ¬grid a}) (_ : O a.val.1) =>
      CoefficientJetScalar a.val)).symm

noncomputable def allocatedLongRealScalarEquiv (q : realOutput) : ℝ ≃ᵐ scalar q.val := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact MeasurableEquiv.refl _
  · exact False.elim (hq ⟨allocatedLongIntegerIndex B U basis S j i ha o, rfl⟩)

noncomputable def allocatedLongIntegerScalarEquiv (q : integerOutput) : ℤ ≃ᵐ scalar (select q) := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact False.elim hq
  · exact MeasurableEquiv.refl _

noncomputable def allocatedLongGridEquiv :
    ((realOutput → ℝ) × (integerOutput → ℤ)) ≃ᵐ AllocatedLongJetRows B U basis S O :=
  ((MeasurableEquiv.piCongrRight (allocatedLongRealScalarEquiv B U basis S)).prodCongr
    (MeasurableEquiv.piCongrRight (allocatedLongIntegerScalarEquiv B U basis S))).trans
    ((selectedDependentEquiv select scalar).trans
      (allocatedLongScalarEquiv B U basis S).symm)

theorem allocatedLongGridEquiv_apply (v : realOutput → ℝ) (k : integerOutput → ℤ) :
    allocatedLongGridEquiv B U basis S (v, k) = allocatedLongRowsFromGrid B U basis S v k := by
  apply (allocatedLongScalarEquiv B U basis S).injective
  simp only [allocatedLongGridEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.apply_symm_apply]
  symm
  apply selectedDependentEquiv_eq_of_coordinates
  · intro q
    rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
    · rfl
    · exact False.elim (hq ⟨allocatedLongIntegerIndex B U basis S j i ha o, rfl⟩)
  · intro q
    rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
    · exact False.elim hq
    · rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

variable [∀ j, DecidableEq (O j)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O))

noncomputable def allocatedLongGridMask (v : realOutput → ℝ) (k : integerOutput → ℤ) : ℝ :=
  ∏ a, allocatedLongJetMask B U basis S x rows modulus residue a
    (allocatedLongRowsFromGrid B U basis S v k a)

noncomputable def allocatedLongGridDensityTest (f : (output → ℝ) → ℝ)
    (v : realOutput → ℝ) (qs : Finset (integerOutput → ℤ)) (φ : (integerOutput → ℤ) → ℂ) : ℂ :=
  (∑ k ∈ qs, ((allocatedLongGridMask B U basis S x rows modulus residue v k *
    f (allocatedLongJetRealCoordinates B U basis S (allocatedLongRowsFromGrid B U basis S v k)) : ℝ) : ℂ) * φ k) /
    ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ)

omit [∀ j, DecidableEq (O j)] [Fintype α] in
theorem allocatedLongGridDensityTest_eq (f : (output → ℝ) → ℝ)
    (v : realOutput → ℝ) (qs : Finset (integerOutput → ℤ)) (φ : (integerOutput → ℤ) → ℂ) :
    allocatedLongGridDensityTest B U basis S x rows modulus residue f v qs φ =
      gridDensityTest (selectedOutputSlice (allocatedLongIntegerSelect B U basis S (O := O)) f v)
        (fun _ => 0) (allocatedLongLatticeScale B U basis S) qs
        (allocatedLongGridMask B U basis S x rows modulus residue v) φ := by
  unfold allocatedLongGridDensityTest gridDensityTest selectedOutputSlice
  rw [allocatedLongLatticeScale_product]
  simp only [allocatedLongRowsFromGrid_realCoordinates]

theorem allocatedLongGridDensityTest_proxy
    (u : PrincipalAxisTuples (α := α) grid (allocatedPrincipalSides B U basis S))
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (v : realOutput → ℝ) (qs : Finset (integerOutput → ℤ)) (φ : (integerOutput → ℤ) → ℂ) :
    allocatedLongGridDensityTest B U basis S x rows modulus residue
        (allocatedContinuousLongJetProxy B U basis S x u rows s hA) v qs φ =
      (∑ k ∈ qs, (allocatedLongJetProxy B U basis S x u rows s hA modulus residue
        (allocatedLongRowsFromGrid B U basis S v k) : ℂ) * φ k) /
        ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ) := by
  unfold allocatedLongGridDensityTest allocatedLongGridMask
  simp only [allocatedLongJetProxy_continuous]

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [Fintype α] in
theorem allocatedLongGridMask_bound {C : ℝ} (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (v : realOutput → ℝ) (k : integerOutput → ℤ) :
    |allocatedLongGridMask B U basis S x rows modulus residue v k| ≤
      C ^ Fintype.card (LayerSamplerAxis I n) := by
  have hr (a : {a // ¬grid a}) :
      0 ≤ allocatedLongJetMask B U basis S x rows modulus residue a
        (allocatedLongRowsFromGrid B U basis S v k a) ∧
      allocatedLongJetMask B U basis S x rows modulus residue a
        (allocatedLongRowsFromGrid B U basis S v k a) ≤ C := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact ⟨zero_le_one, hC⟩
    · exact hm j _
  have hnonneg : 0 ≤ allocatedLongGridMask B U basis S x rows modulus residue v k :=
    Finset.prod_nonneg (fun a _ => (hr a).1)
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ ∏ _a : {a // ¬grid a}, C :=
      Finset.prod_le_prod₀ (fun a _ => (hr a).1) (fun a _ => (hr a).2)
    _ = C ^ Fintype.card {a // ¬grid a} := by simp
    _ ≤ _ := pow_le_pow_right₀ hC (Fintype.card_subtype_le _)

omit [∀ j, DecidableEq (O j)] [Fintype α] in
theorem allocatedLongGridDensityTest_comparison
    (f g : (output → ℝ) → ℝ) {Kf Kg : ℝ≥0} (Ro : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (Ro : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (Ro : ℝ) < ‖v‖ → g v = 0)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    {mesh C : ℝ} (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1)
    (hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
    (hC : 1 ≤ C)
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C)
    (qs : (realOutput → ℝ) → Finset (integerOutput → ℤ))
    (φ : (realOutput → ℝ) → (integerOutput → ℤ) → ℂ)
    (hφ : ∀ v k, k ∈ qs v → ‖φ v k‖ ≤ 1) :
    ‖∫ v, allocatedLongGridDensityTest B U basis S x rows modulus residue f v (qs v) (φ v) -
      allocatedLongGridDensityTest B U basis S x rows modulus residue g v (qs v) (φ v)‖ ≤
      C ^ Fintype.card (LayerSamplerAxis I n) *
        (ε + (2 * (Ro : ℝ)) ^ Fintype.card realOutput *
          ((2 * (Ro : ℝ) + 2) ^ Fintype.card integerOutput * ((Kf : ℝ) + Kg) * mesh)) := by
  simp_rw [allocatedLongGridDensityTest_eq]
  exact fixed_mixed_output_grid_error (allocatedLongIntegerSelect B U basis S (O := O))
    f g Ro hf hg hfs hgs hfg he (fun _ _ => 0) (fun _ => allocatedLongLatticeScale B U basis S)
    (fun _ => allocatedLongLatticeScale_pos B U basis S) hmesh0 hmesh1
    (fun _ q => (allocatedLongLatticeScale_mesh B U basis S q).trans hmesh) qs
    (allocatedLongGridMask B U basis S x rows modulus residue) φ
    (pow_nonneg (zero_le_one.trans hC) _)
    (fun v k _ => allocatedLongGridMask_bound B U basis S x rows modulus residue hC hm v k) hφ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "select" => allocatedLongIntegerSelect B U basis S (O := O)
local notation "realOutput" => UnselectedColumn select
local notation "scalar" => fun q : output => CoefficientJetScalar (Subtype.val (Sigma.fst q))
local notation "law" => fun q : output => coefficientJetScalarReference (Subtype.val (Sigma.fst q))

theorem allocatedLongScalarEquiv_measurePreserving :
    MeasurePreserving (allocatedLongScalarEquiv B U basis S (O := O))
      (allocatedLongJetReference B U basis S O) (Measure.pi law) := by
  have hrows := measurePreserving_pi
    (fun a : {a // ¬grid a} => coefficientJetAxisReference O a.val)
    (fun a : {a // ¬grid a} => Measure.pi (fun _ : O a.val.1 => coefficientJetScalarReference a.val))
    (fun a => coefficientJetScalarEquiv_measurePreserving O a.val)
  have hflat : MeasurePreserving
      (MeasurableEquiv.piCurry (fun (a : {a // ¬grid a}) (_ : O a.val.1) =>
        CoefficientJetScalar a.val)).symm
      (Measure.pi (fun a : {a // ¬grid a} =>
        Measure.pi (fun _ : O a.val.1 => coefficientJetScalarReference a.val)))
      (Measure.pi law) :=
    ⟨(MeasurableEquiv.piCurry (fun (a : {a // ¬grid a}) (_ : O a.val.1) =>
      CoefficientJetScalar a.val)).symm.measurable, sigmaFiniteProductMeasure_flatten law⟩
  exact hflat.comp hrows

omit [∀ j, Fintype (O j)] in
theorem allocatedLongRealScalarEquiv_measurePreserving (q : realOutput) :
    MeasurePreserving (allocatedLongRealScalarEquiv B U basis S q) volume (law q.val) := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact MeasurePreserving.id volume
  · exact False.elim (hq ⟨allocatedLongIntegerIndex B U basis S j i ha o, rfl⟩)

omit [∀ j, Fintype (O j)] in
theorem allocatedLongIntegerScalarEquiv_measurePreserving (q : integerOutput) :
    MeasurePreserving (allocatedLongIntegerScalarEquiv B U basis S q) Measure.count
      (law (select q)) := by
  rcases q with ⟨⟨⟨⟨j, i | i⟩, ha⟩, o⟩, hq⟩
  · exact False.elim hq
  · exact MeasurePreserving.id Measure.count

theorem allocatedLongGridEquiv_measurePreserving :
    MeasurePreserving (allocatedLongGridEquiv B U basis S (O := O))
      ((volume : Measure (realOutput → ℝ)).prod (Measure.count : Measure (integerOutput → ℤ)))
      (allocatedLongJetReference B U basis S O) := by
  have hr := measurePreserving_pi (fun _ : realOutput => (volume : Measure ℝ))
    (fun q => law q.val) (allocatedLongRealScalarEquiv_measurePreserving B U basis S)
  have hi := measurePreserving_pi (fun _ : integerOutput => (Measure.count : Measure ℤ))
    (fun q => law (select q)) (allocatedLongIntegerScalarEquiv_measurePreserving B U basis S)
  have hcoords : MeasurePreserving
      ((MeasurableEquiv.piCongrRight (allocatedLongRealScalarEquiv B U basis S)).prodCongr
        (MeasurableEquiv.piCongrRight (allocatedLongIntegerScalarEquiv B U basis S)))
      ((volume : Measure (realOutput → ℝ)).prod (Measure.count : Measure (integerOutput → ℤ)))
      ((Measure.pi (fun q : realOutput => law q.val)).prod
        (Measure.pi (fun q : integerOutput => law (select q)))) := by
    have h := hr.prod hi
    rw [pi_count_measure] at h
    exact h
  unfold allocatedLongGridEquiv
  rw [MeasurableEquiv.coe_trans, MeasurableEquiv.coe_trans]
  exact (((allocatedLongScalarEquiv_measurePreserving B U basis S (O := O)).symm
    (allocatedLongScalarEquiv B U basis S)).comp
      (selectedDependentEquiv_measurePreserving select scalar law)).comp hcoords

theorem allocatedLongGridEquiv_coe :
    (allocatedLongGridEquiv B U basis S (O := O) :
      ((realOutput → ℝ) × (integerOutput → ℤ)) → AllocatedLongJetRows B U basis S O) =
      fun p => allocatedLongRowsFromGrid B U basis S p.1 p.2 := by
  funext p
  rcases p with ⟨v, k⟩
  exact allocatedLongGridEquiv_apply B U basis S v k

theorem allocatedLongRowsFromGrid_measurePreserving :
    MeasurePreserving
      (fun p : (realOutput → ℝ) × (integerOutput → ℤ) =>
        allocatedLongRowsFromGrid B U basis S p.1 p.2)
      ((volume : Measure (realOutput → ℝ)).prod (Measure.count : Measure (integerOutput → ℤ)))
      (allocatedLongJetReference B U basis S O) := by
  rw [← allocatedLongGridEquiv_coe]
  exact allocatedLongGridEquiv_measurePreserving B U basis S

theorem allocatedLongRowsFromGrid_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AllocatedLongJetRows B U basis S O → E) :
    (∫ p : (realOutput → ℝ) × (integerOutput → ℤ),
      f (allocatedLongRowsFromGrid B U basis S p.1 p.2) ∂volume.prod Measure.count) =
      ∫ z, f z ∂allocatedLongJetReference B U basis S O := by
  have h := (allocatedLongGridEquiv_measurePreserving B U basis S (O := O)).integral_comp
    (allocatedLongGridEquiv B U basis S).measurableEmbedding f
  simpa only [allocatedLongGridEquiv_coe] using h

theorem allocatedLongRowsFromGrid_integrable_iff
    {E : Type*} [NormedAddCommGroup E] (f : AllocatedLongJetRows B U basis S O → E) :
    Integrable (fun p : (realOutput → ℝ) × (integerOutput → ℤ) =>
      f (allocatedLongRowsFromGrid B U basis S p.1 p.2)) (volume.prod Measure.count) ↔
      Integrable f (allocatedLongJetReference B U basis S O) := by
  have h := (allocatedLongGridEquiv_measurePreserving B U basis S (O := O)).integrable_comp_emb
    (allocatedLongGridEquiv B U basis S).measurableEmbedding (g := f)
  simpa only [allocatedLongGridEquiv_coe, Function.comp_def] using h

theorem allocatedLongRowsFromGrid_integral_finset
    (f : AllocatedLongJetRows B U basis S O → ℂ)
    (hf : Integrable f (allocatedLongJetReference B U basis S O))
    (qs : (realOutput → ℝ) → Finset (integerOutput → ℤ))
    (hs : ∀ v k, k ∉ qs v → f (allocatedLongRowsFromGrid B U basis S v k) = 0) :
    (∫ z, f z ∂allocatedLongJetReference B U basis S O) =
      ∫ v, ∑ k ∈ qs v, f (allocatedLongRowsFromGrid B U basis S v k) := by
  rw [← allocatedLongRowsFromGrid_integral B U basis S f]
  rw [integral_prod _ ((allocatedLongRowsFromGrid_integrable_iff B U basis S f).mpr hf)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  have hi : Integrable (fun k => f (allocatedLongRowsFromGrid B U basis S v k))
      Measure.count := by
    apply integrable_count_iff.mpr
    exact (hasSum_sum_of_ne_finset_zero (fun k hk => by rw [hs v k hk, norm_zero])).summable
  rw [integral_countable hi]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  exact (hasSum_sum_of_ne_finset_zero (hs v)).tsum_eq

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped ContDiff NNReal Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] [∀ j, Nonempty (O j)]

local notation "hLayer" => layerSamplerDegree I n

theorem exists_allocated_long_grid_comparison
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ δ ≤ 1 ∧
      (δ : ℝ) = booleanRegularizationRadius (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T (ε / 2) ∧
      let t := booleanMassPerturbationScale (B := B)
        (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
        ((G × Option α) ⊕ (Σ d, SamplerCoefficientSlot G B hLayer d)) hLayer
        (unitProfilePrincipalSize (B := B)) (fun d => 2 * unitProfilePrincipalSize (B := B) d)
        A T m 1 (ε / 2)
      0 < t ∧ t ≤ 1 ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R : Fin m → ℝ} (hR : ∀ j, 0 < R j)
        {σ : Fin m → ℝ} (_hσ : ∀ j, 0 < σ j) (_hσt : ∀ j, σ j ≤ t)
        (S : LayerSamplerScale (G := G) B U basis R σ)
        (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
          (allocatedPrincipalSides B U basis S))
        (rows : ∀ j, O j → Finset α)
        (_hrows : ∀ j, Function.Injective (rows j))
        (_hcard : ∀ j o, (rows j o).card ≤ j.val + 1)
        (_block : ∀ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1 ↪ B a.val)
        (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
        {M : ℕ} (_hM : 0 < M)
        (_hi : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j) (s j) (hA j) (1 / (M : ℝ)))
        {P : ℝ} (_hP : 0 ≤ P) (_hMP : (M : ℝ) ≤ Real.exp P)
        (_hRP : ∀ j, R j ≤ Real.exp P) (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)
        (modulus : ℕ)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
        {mesh C : ℝ} (_hmesh0 : 0 ≤ mesh) (_hmesh1 : mesh ≤ 1)
        (_hmesh : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh) (_hC : 1 ≤ C)
        (_hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (residue j) z ≤ C),
      let ideal := physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) hLayer
        (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
        (fun a => R a.1) (fun a => hR a.1) δ
      let proxy := allocatedContinuousLongJetProxy B U basis S x u rows s hA
      let Q := {q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) //
        allocatedLongIntegerCoordinate B U basis S q}
      let select := allocatedLongIntegerSelect B U basis S (O := O)
      let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O P), (Real.exp_pos _).le⟩
      let Kp : ℝ≥0 := (Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound *
        bound ^ Fintype.card (LayerSamplerAxis I n)
      let Ki : ℝ≥0 := ‖(∏ q : (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1),
        R q.1.val.1)⁻¹‖₊ *
        (affineProductProfileLip (Σ a : {a // ¬allocatedGridAxis (I := I) U basis S.value a}, O a.val.1) δ *
          (NNReal.mk (Real.exp P) (Real.exp_pos P).le))
      let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
        (Real.exp P * (partitionedIdealRadius α m + 1)))
      ∀ (qs : (UnselectedColumn select → ℝ) → Finset (Q → ℤ))
        (φ : (UnselectedColumn select → ℝ) → (Q → ℤ) → ℂ),
      (∀ v k, k ∈ qs v → ‖φ v k‖ ≤ 1) →
      ‖∫ v, allocatedLongGridDensityTest B U basis S x rows modulus residue proxy v (qs v) (φ v) -
        allocatedLongGridDensityTest B U basis S x rows modulus residue ideal v (qs v) (φ v)‖ ≤
        C ^ Fintype.card (LayerSamplerAxis I n) *
          (ε + (2 * (Ro : ℝ)) ^ Fintype.card (UnselectedColumn select) *
            ((2 * (Ro : ℝ) + 2) ^ Fintype.card Q * ((Kp : ℝ) + Ki) * mesh)) := by
  obtain ⟨δ, hδ, hδ1, hδeq, ht, ht1, hcompare⟩ := exists_allocated_proxy_l1_comparison
    (G := G) (α := α) (O := O) B ψ hψ hrange hzero hone A T hLip hTransition hε
  refine ⟨δ, hδ, hδ1, hδeq, ht, ht1, ?_⟩
  intro J _ U basis R hR σ hσ hσt S x u rows hrows hcard block s hA
    M hM hi P hP hMP hRP hRi hσi hcount modulus residue mesh C hmesh0 hmesh1 hmesh hC hm
  dsimp only
  intro qs φ hφ
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσt j).trans ht1
  have hL1 := (hcompare U basis hR hσ hσt S x u rows hrows hcard block s hA).1
  have hp := allocatedContinuousLongJetProxy_output_bounds B U basis hR hσ S x rows s hA
    hM hi hP hMP hRP hRi hσi hcount u hσ1
  have hip := physicalActiveProfileIdeal_probability (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ
  have hpp := allocatedContinuousLongJetProxy_probability B U basis hR hσ S x u rows s hA hσ1
  have hil := physicalActiveProfileIdeal_lipschitz (G := G) (B := B) (G × Option α)
    hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
    (fun a => R a.1) (fun a => hR a.1) δ hδ ⟨Real.exp P, (Real.exp_pos P).le⟩ (fun a => hRi a.1)
  let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O P))
    (Real.exp P * (partitionedIdealRadius α m + 1)))
  have hRoP : Real.exp (allocatedJetSupportLog (G := G) B α O P) ≤ (Ro : ℝ) :=
    (le_max_left _ _).trans (Real.le_coe_toNNReal _)
  have hRoI : Real.exp P * (partitionedIdealRadius α m + 1) ≤ (Ro : ℝ) :=
    (le_max_right _ _).trans (Real.le_coe_toNNReal _)
  apply allocatedLongGridDensityTest_comparison B U basis S x rows modulus residue
    _ _ Ro hp.2 hil
    (fun v hv => allocatedContinuousLongJetProxy_zero_off_ball B U basis hR hσ S x rows s hA
      hM hi hP hMP hRP hRi hσi hcount u hσ1 v (hRoP.trans_lt hv))
    (fun v hv => physicalActiveProfileIdeal_zero_outside (G := G) (B := B) (G × Option α)
      hLayer (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1)
      (fun a => R a.1) (fun a => hR a.1)
      (fun a => Nat.succ_le_of_lt a.1.isLt) δ hδ hδ1
      ⟨Real.exp P, (Real.exp_pos P).le⟩ (fun a => hRP a.1) v (hRoI.trans_lt hv))
    (hpp.2.1.sub hip.2.1) _ hmesh0 hmesh1 hmesh hC hm qs φ hφ
  simpa only [abs_sub_comm] using hL1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value) (rows : ∀ j, O j → Finset α)
variable (modulus : ℕ)
variable (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "integerOutput" => {q : output // allocatedLongIntegerCoordinate B U basis S q}
local notation "realOutput" => UnselectedColumn (allocatedLongIntegerSelect B U basis S (O := O))

theorem allocatedLongRowsFromGrid_zero_off_indices
    (f : (output → ℝ) → ℝ) {Ro : ℝ} (hs : ∀ z, Ro < ‖z‖ → f z = 0)
    (v : realOutput → ℝ) (k : integerOutput → ℤ)
    (hk : k ∉ rectangularWeightIndices (fun _ => 0) (allocatedLongLatticeScale B U basis S) Ro) :
    f (allocatedLongJetRealCoordinates B U basis S (allocatedLongRowsFromGrid B U basis S v k)) = 0 := by
  rw [allocatedLongRowsFromGrid_realCoordinates]
  change rectangularWeight
    (selectedOutputSlice (allocatedLongIntegerSelect B U basis S (O := O)) f v)
    (fun _ => 0) (allocatedLongLatticeScale B U basis S) k = 0
  exact rectangularWeight_zero_off_indices _ _ _ (allocatedLongLatticeScale_pos B U basis S)
    (selectedOutputSlice_support_right (allocatedLongIntegerSelect B U basis S (O := O)) hs v) k hk

theorem allocatedLongGridDensityTest_integral
    (f : (output → ℝ) → ℝ) (φ : AllocatedLongJetRows B U basis S O → ℂ)
    (qs : (realOutput → ℝ) → Finset (integerOutput → ℤ))
    (hs : ∀ v k, k ∉ qs v →
      f (allocatedLongJetRealCoordinates B U basis S (allocatedLongRowsFromGrid B U basis S v k)) = 0)
    (hi : Integrable (fun z : AllocatedLongJetRows B U basis S O =>
      (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        f (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z /
        ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ))
      (allocatedLongJetReference B U basis S O)) :
    (∫ z : AllocatedLongJetRows B U basis S O,
      (((∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
        f (allocatedLongJetRealCoordinates B U basis S z) : ℝ) : ℂ) * φ z /
        ((∏ a : {a // ¬grid a}, allocatedLongJetOutputScale B U basis S (O := O) a : ℝ) : ℂ)
      ∂allocatedLongJetReference B U basis S O) =
      ∫ v, allocatedLongGridDensityTest B U basis S x rows modulus residue f v (qs v)
        (fun k => φ (allocatedLongRowsFromGrid B U basis S v k)) := by
  rw [allocatedLongRowsFromGrid_integral_finset B U basis S _ hi qs (by
    intro v k hk
    rw [hs v k hk]
    simp)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  simp only [allocatedLongGridDensityTest, allocatedLongGridMask, Finset.sum_div]

end Erdos3.VectorPolynomial

end

end OAI
