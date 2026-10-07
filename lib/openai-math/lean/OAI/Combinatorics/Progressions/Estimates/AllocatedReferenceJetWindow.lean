import OAI.Combinatorics.Progressions.Geometry.AllocatedSpatialProxyCap

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

def translatePhysicalCube {X α : Type*} (base : X → ℤ)
    (v : X → (Unit ⊕ α) → ℤ) : X → (Unit ⊕ α) → ℤ :=
  fun x i => physicalCubeOffset base x i + v x i

theorem physicalCubeVertexValue_translate {X α : Type*} (base : X → ℤ)
    (v : X → (Unit ⊕ α) → ℤ) (s : Finset α) :
    physicalCubeVertexValue (translatePhysicalCube base v) s =
      fun x => base x + physicalCubeVertexValue v s x := by
  funext x
  simp only [physicalCubeVertexValue, translatePhysicalCube, physicalCubeOffset,
    zero_add, add_assoc]

theorem physicalResidueReconstruction_translate {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (v : X → (Unit ⊕ α) → ℤ) :
    physicalResidueReconstruction root D base r q v =
      translatePhysicalCube base (physicalResidueReconstruction root D 0 r q v) := by
  funext x i
  cases i <;> simp [physicalResidueReconstruction, physicalCubeRootDifferences,
    translatePhysicalCube, physicalCubeOffset, add_assoc]

theorem physicalCubeCoveredSample_translate {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (cover : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (base : X → ℤ)
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalCubeCoveredSample U cover
        (fun j => translate (fun x => (base x : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j)) v =
      physicalCubeCoveredSample U cover p hm (translatePhysicalCube base v) := by
  funext j
  dsimp only [physicalCubeCoveredSample]
  apply congrArg (QuotientAddGroup.mk' (subspaceArrayIntegerLattice (Finset (Fin q)) (U j)))
  apply congrArg (fun w : Finset (Fin q) → U j => (cover : ℝ)⁻¹ • w)
  funext s
  apply Subtype.ext
  rw [eval_restrictCoefficients, eval_restrictCoefficients, eval_translate]
  apply congrArg (fun x : X → ℝ => eval x (p j))
  funext x
  rw [physicalCubeVertexValue_translate]
  simp only [Int.cast_add, add_comm]

theorem physicalCubeEuclideanSample_translate {X : Type*} {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (cover : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (base : X → ℤ)
    (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalCubeEuclideanSample U cover
        (fun j => translate (fun x => (base x : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j)) v =
      physicalCubeEuclideanSample U cover p hm (translatePhysicalCube base v) := by
  unfold physicalCubeEuclideanSample
  rw [physicalCubeCoveredSample_translate]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem physicalCubeRowSample_translate {X : Type*} {m dim : ℕ}
    {J O : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (O j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (d : ℕ)
    (rows : ∀ j, O j → Finset (Fin dim))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (base : X → ℤ)
    (v : X → (Unit ⊕ Fin dim) → ℤ) :
    physicalCubeRowSample U d rows
        (fun j => translate (fun x => (base x : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j)) v =
      physicalCubeRowSample U d rows p hm (translatePhysicalCube base v) := by
  unfold physicalCubeRowSample
  rw [physicalCubeCoveredSample_translate]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem physicalResidueReconstruction_injective {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (q : X → ℕ) (hq : ∀ x, 0 < q x) :
    Function.Injective (physicalResidueReconstruction root D base r q) := by
  intro v w h
  funext x i
  have he := congrFun (congrFun h x) i
  have hn : (q x : ℤ) ≠ 0 := by exact_mod_cast (hq x).ne'
  exact mul_left_cancel₀ hn (add_left_cancel he)

theorem physicalResidueReconstruction_columnResidue {K X : Type*} [Fintype K] {q : ℕ}
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (stride : X → ℕ) (v : X → (Unit ⊕ Fin q) → ℤ) :
    columnResiduePattern stride
        (standardPhysicalCubeFrame (physicalResidueReconstruction root D base r stride v)) =
      columnResiduePattern stride (standardPhysicalCubeFrame (physicalCubeRootDifferences root D base r)) := by
  funext z
  rcases z with ⟨k,x⟩
  cases k <;> simp [columnResiduePattern, standardPhysicalCubeFrame,
    physicalResidueReconstruction]

theorem physicalResidueReconstruction_jet_sum {K X : Type*} [Fintype K] [Fintype X] [DecidableEq X]
    {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (cover : ℕ)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, VectorPolynomial.coefficients (p j) e ∈ U j)
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (base : X → ℤ)
    (r : Option K × X → ℤ) (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (g : EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ)
    (window : Finset (X → (Unit ⊕ Fin q) → ℤ)) :
    (∑ v ∈ window.image (physicalResidueReconstruction root D 0 r stride),
      g (physicalCubeEuclideanSample U cover
        (fun j => VectorPolynomial.translate (fun x => (base x : ℝ)) (p j))
        (fun j => VectorPolynomial.coefficients_translate_mem (U j)
          (fun x => (base x : ℝ)) (p j) (hm j)) v)) =
      ∑ v ∈ window, g (physicalCubeEuclideanSample U cover p hm
        (physicalResidueReconstruction root D base r stride v)) := by
  classical
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro v _
    apply congrArg g
    rw [physicalCubeEuclideanSample_translate, ← physicalResidueReconstruction_translate]
  · intro v _ w _ he
    exact physicalResidueReconstruction_injective root D 0 r stride hs he

theorem spatialWindow_four_coordinate_bound {X α : Type*} [Fintype X] [Fintype α]
    (H : X → ℝ) (hH : ∀ x, 0 ≤ H x) {v : X → (Unit ⊕ α) → ℤ}
    (hv : v ∈ spatialWindow H 4) (x : X) (i : Unit ⊕ α) :
    |(v x i : ℝ)| ≤ 8 * H x := by
  have h := (mem_spatialWindow_iff H 4 v).mp hv
  have hr : |(v x (.inl ()) : ℝ)| ≤ H x * 4 := h x (.inl ())
  cases i with
  | inl i => cases i; nlinarith [hH x]
  | inr i =>
    have hd : |(v x (.inl ()) : ℝ) + (v x (.inr i) : ℝ)| ≤ H x * 4 := by
      simpa only [spatialStar, Sum.elim_inr, Int.cast_add] using h x (.inr i)
    rcases abs_le.mp hr with ⟨hr₁,hr₂⟩
    rcases abs_le.mp hd with ⟨hd₁,hd₂⟩
    apply abs_le.mpr
    constructor <;> linarith

theorem physicalCube_zero_residue_bound {K X α : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (stride : X → ℕ)
    (r : Option K × X → ℤ) (hr : ∀ k x, |(r (k,x) : ℝ)| ≤ stride x)
    (H : X → ℝ)
    (hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (x : X) (i : Unit ⊕ α) :
    |(physicalCubeRootDifferences root D 0 r x i : ℝ)| ≤ (stride x : ℝ) * H x := by
  have hz : physicalCubeOffset (0 : X → ℤ) x i = 0 := by cases i <;> rfl
  simp only [physicalCubeRootDifferences, hz, zero_add, Int.cast_sum, Int.cast_mul]
  calc
    _ ≤ ∑ k, |(physicalCubeCoefficient root D i k : ℝ) * (r (k,x) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |(physicalCubeCoefficient root D i k : ℝ)| * |(r (k,x) : ℝ)| := by
      simp only [abs_mul]
    _ ≤ ∑ k, |(physicalCubeCoefficient root D i k : ℝ)| * (stride x : ℝ) := by
      exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hr k x) (abs_nonneg _))
    _ = (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) * (stride x : ℝ) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ H x * (stride x : ℝ) := mul_le_mul_of_nonneg_right (hrows x i) (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

noncomputable def referenceJetEnvelopeWidths {X : Type*} {q : ℕ}
    (stride : X → ℕ) (H : X → ℝ) : Option (Fin q) × X → ℝ :=
  fun z => 20 * (stride z.2 : ℝ) * H z.2

theorem referenceJetEnvelopeWidths_pos {X : Type*} {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H : X → ℝ) (hH : ∀ x, 0 < H x)
    (z : Option (Fin q) × X) : 0 < referenceJetEnvelopeWidths stride H z := by
  exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr (hs z.2))) (hH z.2)

theorem referenceJetEnvelopeWidths_residue {X : Type*} {q : ℕ}
    (stride : X → ℕ) (hs : ∀ x, 0 < stride x) (H : X → ℝ) (z : Option (Fin q) × X) :
    residueProfileWidth stride (referenceJetEnvelopeWidths stride H) z = 20 * H z.2 := by
  have hn : (stride z.2 : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hs z.2)).ne'
  dsimp only [residueProfileWidth, referenceJetEnvelopeWidths]
  field_simp

theorem physicalResidueReconstruction_envelope {K X : Type*} [Fintype K] [Fintype X] {q : ℕ}
    (root : K → ℤ) (D : Matrix (Fin q) K ℤ) (stride : X → ℕ) (hs : ∀ x, 0 < stride x)
    (r : Option K × X → ℤ) (H : X → ℝ) (hH : ∀ x, 0 < H x)
    (hoffset : ∀ x i, |(physicalCubeRootDifferences root D 0 r x i : ℝ)| ≤ (stride x : ℝ) * H x)
    {v : X → (Unit ⊕ Fin q) → ℤ} (hv : v ∈ spatialWindow H 4)
    (z : Option (Fin q) × X) :
    |(standardPhysicalCubeFrame (physicalResidueReconstruction root D 0 r stride v) z : ℝ) /
      referenceJetEnvelopeWidths stride H z| ≤ 1 / 2 := by
  have hcoord (i : Unit ⊕ Fin q) :
      |(physicalResidueReconstruction root D 0 r stride v z.2 i : ℝ)| ≤
        9 * (stride z.2 : ℝ) * H z.2 := by
    simp only [physicalResidueReconstruction, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (stride z.2) : (0 : ℝ) ≤ stride z.2)]
    have h := mul_le_mul_of_nonneg_left
      (spatialWindow_four_coordinate_bound H (fun x => (hH x).le) hv z.2 i)
      (Nat.cast_nonneg (stride z.2) : (0 : ℝ) ≤ stride z.2)
    linarith [hoffset z.2 i]
  have hf : |(standardPhysicalCubeFrame (physicalResidueReconstruction root D 0 r stride v) z : ℝ)| ≤
      9 * (stride z.2 : ℝ) * H z.2 := by
    rcases z with ⟨k,x⟩
    cases k with
    | none => exact hcoord (.inl ())
    | some k => exact hcoord (.inr k)
  rw [abs_div, abs_of_pos (referenceJetEnvelopeWidths_pos stride hs H hH z),
    div_le_iff₀ (referenceJetEnvelopeWidths_pos stride hs H hH z)]
  dsimp only [referenceJetEnvelopeWidths]
  nlinarith [mul_pos (Nat.cast_pos.mpr (hs z.2) : (0 : ℝ) < stride z.2) (hH z.2)]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem referenceJetEnvelopeWidths_trimmed {X : Type*} {q : ℕ}
    (stride N : X → ℕ) (hs : ∀ x, 0 < stride x) (τ : ℝ) (z : Option (Fin q) × X) :
    referenceJetEnvelopeWidths stride (trimmedSpatialRootScale τ N stride) z =
      (5 / 2 : ℝ) * τ * (N z.2 : ℝ) := by
  have hn : (stride z.2 : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hs z.2)).ne'
  dsimp only [referenceJetEnvelopeWidths, trimmedSpatialRootScale]
  field_simp
  ring

end Erdos3.BooleanCubeKernel

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox α S.value)

theorem allocatedPhysicalCube_coefficient_row_sum
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (i : Unit ⊕ α) :
    (∑ k, |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)|) ≤
      Fintype.card (Option (LayerSamplerVariables G I n B)) * allocatedPhysicalEntryBudget B U basis S c := by
  calc
    _ ≤ ∑ _k : Option (LayerSamplerVariables G I n B), allocatedPhysicalEntryBudget B U basis S c :=
      Finset.sum_le_sum (fun k _ => allocatedPhysicalCube_coefficient_entry_bound B U basis S c x y i k)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem allocatedNarrow_reference_jet_geometry
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    {X : Type*} (N stride : X → ℕ) (hN : ∀ t, 0 < N t) (hs : ∀ t, 0 < stride t)
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (hρ : 0 < ρ)
    (hsize : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ ρ) (t : X) :
    let H := trimmedSpatialRootScale τ N stride
    0 < H t ∧
      (∀ i, (∑ k, |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
        (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)|) ≤ H t) ∧
      τ * (N t : ℝ) ≤ 20 * (stride t : ℝ) * H t ∧
      8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t := by
  intro H
  have hH : ρ ≤ H t :=
    (narrowTrimmedSpatial_scale_lower hW hτ hξ1 hρ.le N stride t (hN t) (hs t) (hsize t)).1
  have hpos : 0 < H t := hρ.trans_le hH
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro i
    apply (allocatedPhysicalCube_coefficient_row_sum B U basis S c x y i).trans
    have he : 0 ≤ allocatedPhysicalEntryBudget B U basis S c :=
      zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U basis S c)
    have hc := mul_nonneg (Nat.cast_nonneg (Fintype.card (Option (LayerSamplerVariables G I n B))) :
      (0 : ℝ) ≤ Fintype.card (Option (LayerSamplerVariables G I n B))) he
    nlinarith
  · have he := referenceJetEnvelopeWidths_trimmed (q := 0) stride N hs τ (none,t)
    change 20 * (stride t : ℝ) * H t = (5 / 2 : ℝ) * τ * (N t : ℝ) at he
    rw [he]
    nlinarith [mul_nonneg hτ.le (Nat.cast_nonneg (N t) : (0 : ℝ) ≤ N t)]
  · exact hρ8.trans (hH.trans (by linarith))

theorem allocatedNarrow_reference_comparison_geometry
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    {X : Type*} (N stride : X → ℕ) (hN : ∀ t, 0 < N t) (hs : ∀ t, 0 < stride t)
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ t, 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ * τ) * (N t : ℝ))
    (hρ8 : 8 * (probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U basis S c)) ≤ ρ) :
    let H := trimmedSpatialRootScale τ N stride
    (∀ t i, (∑ k, |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)|) ≤ H t) ∧
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) ∧
    (∀ t, 1 ≤ H t) := by
  intro H
  have he := allocatedPhysicalEntryBudget_one_le B U basis S c
  have hc : (1 : ℝ) ≤ Fintype.card (Option (LayerSamplerVariables G I n B)) := by
    rw [Fintype.card_option, Nat.cast_add, Nat.cast_one]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  have hprod := mul_le_mul hc (show (1 : ℝ) ≤ allocatedPhysicalEntryBudget B U basis S c from he)
    zero_le_one (Nat.cast_nonneg _)
  have hρ : 1 ≤ ρ := by nlinarith only [hρshift, hprod]
  have hgeom (t : X) := allocatedNarrow_reference_jet_geometry B U basis S c x y N stride hN hs
    hW hτ hξ1 (zero_lt_one.trans_le hρ) hsize hρ8 hρshift t
  refine ⟨fun t => (hgeom t).2.1, fun t => (hgeom t).2.2.2, ?_⟩
  intro t
  exact hρ.trans (narrowTrimmedSpatial_scale_lower hW hτ hξ1
    (zero_le_one.trans hρ) N stride t (hN t) (hs t) (hsize t)).1

end Erdos3.VectorPolynomial

end

end OAI
