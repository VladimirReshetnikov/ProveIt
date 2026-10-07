/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedReferenceWindowTest
import OAI.Combinatorics.Progressions.Probability.AllocatedNarrowSpatialLaw

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {Ω R : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq R]
variable (p : FiniteProbabilityWeights Ω) (label : Ω → R)

noncomputable def supportedFiberReference (r : R) : Ω :=
  if h : 0 < p.mass (Finset.univ.filter (fun x => label x = r)) then
    (p.condition _ h).exists_weight_pos.choose
  else p.exists_weight_pos.choose

theorem supportedFiberReference_positive (r : R)
    (hr : 0 < p.mass (Finset.univ.filter (fun x => label x = r))) :
    label (p.supportedFiberReference label r) = r ∧ p.weight (p.supportedFiberReference label r) ≠ 0 := by
  unfold supportedFiberReference
  rw [dite_eq_left hr]
  have h := condition_weight_support p _ hr (p.condition _ hr).exists_weight_pos.choose
    (p.condition _ hr).exists_weight_pos.choose_spec.ne'
  exact ⟨(Finset.mem_filter.mp h.1).2, h.2⟩

theorem supportedFiberReference_weight (r : R) :
    p.weight (p.supportedFiberReference label r) ≠ 0 := by
  by_cases hr : 0 < p.mass (Finset.univ.filter (fun x => label x = r))
  · exact (p.supportedFiberReference_positive label r hr).2
  · simpa only [supportedFiberReference, dite_eq_right hr] using p.exists_weight_pos.choose_spec.ne'

theorem supportedFiberReference_label (x : Ω) (hx : p.weight x ≠ 0) :
    label (p.supportedFiberReference label (label x)) = label x := by
  have hp : 0 < p.weight x := lt_of_le_of_ne (p.nonneg x) (Ne.symm hx)
  have hm : 0 < p.mass (Finset.univ.filter (fun y => label y = label x)) :=
    hp.trans_le (p.weight_le_mass _ (Finset.mem_filter.mpr ⟨Finset.mem_univ x, rfl⟩))
  exact (p.supportedFiberReference_positive label (label x) hm).1

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open BooleanCubeKernel

noncomputable def narrowTrimmedSpatialWidths {G J X : Type*}
    (W τ ξ : ℝ) (N : X → ℕ) : Option (G ⊕ J) × X → ℝ :=
  fun z => match z.1 with
    | some (.inr _) => ξ * trimmedSpatialWidths W τ N z
    | _ => trimmedSpatialWidths W τ N z

theorem narrowTrimmedSpatialWidths_pos {G J X : Type*}
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (z : Option (G ⊕ J) × X) :
    0 < narrowTrimmedSpatialWidths W τ ξ N z := by
  rcases z with ⟨_ | (g | j), x⟩
  · exact trimmedSpatialWidths_pos hW hτ N hN _
  · exact trimmedSpatialWidths_pos hW hτ N hN _
  · exact mul_pos hξ (trimmedSpatialWidths_pos hW hτ N hN _)

theorem narrowTrimmedSpatialWidths_le {G J X : Type*}
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (z : Option (G ⊕ J) × X) :
    narrowTrimmedSpatialWidths W τ ξ N z ≤ trimmedSpatialWidths W τ N z := by
  rcases z with ⟨_ | (g | j), x⟩
  · exact le_rfl
  · exact le_rfl
  · exact mul_le_of_le_one_left (trimmedSpatialWidths_pos hW hτ N hN _).le hξ1

theorem narrowTrimmedSpatialWidths_lower {G J X : Type*}
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (N : X → ℕ) (hN : ∀ x, 0 < N x) (z : Option (G ⊕ J) × X) :
    trimmedSpatialWidths W (ξ * τ) N z ≤ narrowTrimmedSpatialWidths W τ ξ N z := by
  have he : trimmedSpatialWidths W (ξ * τ) N z = ξ * trimmedSpatialWidths W τ N z := by
    unfold trimmedSpatialWidths
    ring
  rw [he]
  rcases z with ⟨_ | (g | j), x⟩
  · exact mul_le_of_le_one_left (trimmedSpatialWidths_pos hW hτ N hN _).le hξ1
  · exact mul_le_of_le_one_left (trimmedSpatialWidths_pos hW hτ N hN _).le hξ1
  · exact le_rfl

theorem narrowTrimmedSpatial_residue_scale {G J X : Type*}
    (W τ ξ : ℝ) (N q : X → ℕ) (x : X) :
    (fun k => residueProfileWidth q (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) (k,x)) =
      splitPhysicalSpatialInputScale G J (trimmedSpatialRootScale τ N q x)
        (trimmedSpatialSlopeScale W τ N q x) (fun _ => ξ * trimmedSpatialSlopeScale W τ N q x) := by
  funext k
  rcases k with _ | (g | j) <;>
    simp only [residueProfileWidth, narrowTrimmedSpatialWidths, trimmedSpatialWidths,
      centeredSpatialWidths, splitPhysicalSpatialInputScale, trimmedSpatialRootScale,
      trimmedSpatialSlopeScale, one_mul] <;> ring

theorem narrowTrimmedSpatial_scale_lower {X : Type*}
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (hρ : 0 ≤ ρ)
    (N q : X → ℕ) (x : X) (hN : 0 < N x) (hq : 0 < q x)
    (hsize : 8 * (1 + W) * (q x : ℝ) * ρ ≤ (ξ * τ) * (N x : ℝ)) :
    ρ ≤ trimmedSpatialRootScale τ N q x ∧
      ρ ≤ trimmedSpatialSlopeScale W τ N q x ∧
      ρ ≤ ξ * trimmedSpatialSlopeScale W τ N q x := by
  have h := trimmedSpatial_scale_lower hW hρ N q x hq hsize
  have hH : trimmedSpatialRootScale (ξ * τ) N q x = ξ * trimmedSpatialRootScale τ N q x := by
    unfold trimmedSpatialRootScale
    ring
  have hT : trimmedSpatialSlopeScale W (ξ * τ) N q x = ξ * trimmedSpatialSlopeScale W τ N q x := by
    unfold trimmedSpatialSlopeScale
    ring
  rw [hH, hT] at h
  have hp := trimmedSpatial_scales_pos hW hτ N q x hN hq
  exact ⟨h.1.trans (mul_le_of_le_one_left hp.1.le hξ1),
    h.2.trans (mul_le_of_le_one_left hp.2.le hξ1), h.2⟩

theorem narrowTrimmedSpatial_residue_width_lower {G J X : Type*}
    {W τ ξ ρ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (hρ : 0 ≤ ρ)
    (N q : X → ℕ) (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x)
    (hsize : ∀ x, 8 * (1 + W) * (q x : ℝ) * ρ ≤ (ξ * τ) * (N x : ℝ))
    (z : Option (G ⊕ J) × X) :
    ρ ≤ residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N) z := by
  apply (trimmedSpatial_residue_width_lower hW hρ N q hq hsize z).trans
  exact div_le_div_of_nonneg_right (narrowTrimmedSpatialWidths_lower hW hτ hξ1 N hN z)
    (Nat.cast_nonneg _)

namespace BooleanCubeKernel

theorem centeredPhysicalCubeWindow_mono {K X α : Type*}
    [Fintype K] [Fintype X] [Fintype α]
    (root : K → ℤ) (D : Matrix α K ℤ) {V W : Option K × X → ℝ}
    (hVW : ∀ z, V z ≤ W z) :
    centeredPhysicalCubeWindow root D V ⊆ centeredPhysicalCubeWindow root D W := by
  classical
  exact Finset.image_subset_image (rectangularWeightIndices_zero_mono hVW)

theorem narrowTrimmedSpatial_window_subset {G J X α : Type*}
    [Fintype G] [Fintype J] [Fintype X] [Fintype α]
    (root : G ⊕ J → ℤ) (D : Matrix α (G ⊕ J) ℤ)
    {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
    (N q : X → ℕ) (hN : ∀ x, 0 < N x) :
    centeredPhysicalCubeWindow root D (residueProfileWidth q (narrowTrimmedSpatialWidths W τ ξ N)) ⊆
      centeredPhysicalCubeWindow root D (residueProfileWidth q (trimmedSpatialWidths W τ N)) := by
  apply centeredPhysicalCubeWindow_mono
  intro z
  exact div_le_div_of_nonneg_right (narrowTrimmedSpatialWidths_le hW hτ hξ1 N hN z)
    (Nat.cast_nonneg _)

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

variable {G J X : Type*} [Fintype G] [Fintype J] [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ1 : ξ ≤ 1)
variable (N : X → ℕ) (hN : ∀ x, 0 < N x)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))

include hW hτ hξ1 hN hτ1 hsize in
theorem jointIntegerPhysicalSite_narrow_mem_box
    (root : G ⊕ J → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) 1) :
    jointIntegerPhysicalSite root (z.1.val, z.2.val) ∈ integerBox N := by
  have hz : z.2.val ∈ rectangularWeightIndices 0 (trimmedSpatialWidths W τ N) 1 :=
    rectangularWeightIndices_zero_mono (narrowTrimmedSpatialWidths_le hW hτ hξ1 N hN) z.2.property
  exact jointIntegerPhysicalSite_mem_box root N (spatialTrimMargin τ N)
    (fun x => (spatialTrimMargin_proper hτ1 N hN hsize x).le)
    (trimmedSpatialWidths W τ N) (spatialTrimMargin_fits hW hτ.le root hroot N)
    (z.1, ⟨z.2.val, hz⟩)

include hW hτ hξ1 hN hτ1 hsize in
theorem integerBoxTestExtension_joint_narrow
    (root : G ⊕ J → ℤ) (hroot : (∑ k, |(root k : ℝ)|) ≤ W)
    (test : (X → ℝ) → ℂ)
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) 1) :
    integerBoxTestExtension N test (fun x => (jointIntegerPhysicalSite root (z.1.val, z.2.val) x : ℝ)) =
      test (fun x => (jointIntegerPhysicalSite root (z.1.val, z.2.val) x : ℝ)) := by
  exact integerBoxTestExtension_of_mem N test _
    (jointIntegerPhysicalSite_narrow_mem_box hW hτ hξ1 N hN hτ1 hsize root hroot z)

variable {dim : ℕ} (root : G ⊕ J → ℤ) (dirs : Matrix (Fin dim) (G ⊕ J) ℤ)
variable (hsite : ∀ s : Finset (Fin dim), (∑ k, |(integerAffineCube root dirs s k : ℝ)|) ≤ W)

include hW hτ hξ1 hN hτ1 hsize hsite in
theorem physicalCubeSiteTest_narrow_extension
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) 1) :
    physicalCubeSiteTest (fun s => integerBoxTestExtension N (test s))
        (physicalCubeRootDifferences root dirs z.1.val z.2.val) =
      physicalCubeSiteTest test (physicalCubeRootDifferences root dirs z.1.val z.2.val) := by
  unfold physicalCubeSiteTest
  apply Finset.prod_congr rfl
  intro s _
  rw [physicalCubeVertexValue_rootDifferences]
  exact integerBoxTestExtension_joint_narrow hW hτ hξ1 N hN hτ1 hsize
    (integerAffineCube root dirs s) (hsite s) (test s) z

include hW hτ hξ1 hN hτ1 hsize hsite in
theorem physicalCubeSiteTest_narrow_extension_mean
    (law : FiniteProbabilityWeights (trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G) (J := J) W τ ξ N) 1))
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) :
    law.complexMean (fun z => physicalCubeSiteTest (fun s => integerBoxTestExtension N (test s))
        (physicalCubeRootDifferences root dirs z.1.val z.2.val)) =
      law.complexMean (fun z => physicalCubeSiteTest test
        (physicalCubeRootDifferences root dirs z.1.val z.2.val)) := by
  apply congrArg law.complexMean
  funext z
  exact physicalCubeSiteTest_narrow_extension hW hτ hξ1 N hN hτ1 hsize root dirs hsite test z

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (c : LayerSamplerVariables G I n B → ℤ)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hx : ∀ g, (integerScalarCubeWeights (Fin dim) S.value S.positive).weight (x g) ≠ 0)
variable (hy : (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).weight y ≠ 0)

include hx hy in
theorem allocatedPhysicalCube_supported_site_sum (s : Finset (Fin dim)) :
    (∑ k, |(integerAffineCube (allocatedPhysicalCubeRoot B U b S c x y)
      (allocatedPhysicalCubeDirections B U b S x y) s k : ℝ)|) ≤
      allocatedPhysicalRootBudget B U b S c := by
  have hscalar {L : ℕ} (hL : 0 < L) (v : IntegerScalarCubeBox (Fin dim) L)
      (hv : (integerScalarCubeWeights (Fin dim) L hL).weight v ≠ 0) :
      |(integerScalarCubeValue (fun i => (v i : ℤ)) s : ℝ)| ≤ L := by
    have hmem := (condition_weight_support (integerScalarCubeReference (Fin dim) L hL)
      (integerScalarCubeSet (Fin dim) L) (integerScalarCubeReference_mass_pos (Fin dim) L hL) v hv).1
    have hs := ((mem_integerScalarCubeSet L v).mp hmem) s
    have hbound : |integerScalarCubeValue (fun i => (v i : ℤ)) s| ≤ (L : ℤ) := by
      rw [abs_of_nonneg hs.1]
      exact hs.2.le
    exact_mod_cast hbound
  have hyp (j : PrincipalTupleIndex B (layerSamplerDegree I n)) :
      (integerScalarCubeWeights (Fin dim) (allocatedPrincipalSides B U b S j)
        (allocatedPrincipalSides_pos B U b S j)).weight (y j) ≠ 0 := by
    change (∏ j, (integerScalarCubeWeights (Fin dim) (allocatedPrincipalSides B U b S j)
      (allocatedPrincipalSides_pos B U b S j)).weight (y j)) ≠ 0 at hy
    exact Finset.prod_ne_zero_iff.mp hy j (Finset.mem_univ j)
  rw [allocatedPhysicalCube_vertex]
  have hvalue (k : LayerSamplerVariables G I n B) :
      |((Sum.elim (fun g => integerScalarCubeValue (fun i => (x g i : ℤ)) s)
        (fun j => integerScalarCubeValue (fun i => (y j i : ℤ)) s) k : ℤ) : ℝ)| ≤ S.value := by
    cases k with
    | inl g => exact hscalar S.positive (x g) (hx g)
    | inr j =>
      exact (hscalar (allocatedPrincipalSides_pos B U b S j) (y j) (hyp j)).trans
        (Nat.cast_le.mpr (allocatedPrincipalSides_le_scale B U b S j))
  calc
    _ ≤ ∑ k, (|(c k : ℝ)| + (S.value : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _
      push_cast
      exact (abs_add_le _ _).trans (add_le_add le_rfl (hvalue k))
    _ = _ := by simp [allocatedPhysicalRootBudget, Finset.sum_add_distrib]

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {W τ ξ : ℝ} (hbudget : allocatedPhysicalRootBudget B U b S c ≤ W)
variable (hτ : 0 < τ) (hξ1 : ξ ≤ 1) (N : X → ℕ) (hN : ∀ a, 0 < N a)
variable (hτ1 : τ ≤ 1 / 2) (hsize : ∀ a, 4 ≤ τ * (N a : ℝ))

include hx hy hbudget hτ hξ1 hN hτ1 hsize in
theorem allocatedPhysicalCube_supported_testExtension
    (test : Finset (Fin dim) → (X → ℝ) → ℂ)
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G)
        (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) 1) :
    physicalCubeSiteTest (fun s => integerBoxTestExtension N (test s))
        (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S c x y)
          (allocatedPhysicalCubeDirections B U b S x y) z.1.val z.2.val) =
      physicalCubeSiteTest test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S c x y)
        (allocatedPhysicalCubeDirections B U b S x y) z.1.val z.2.val) := by
  exact physicalCubeSiteTest_narrow_extension
    ((allocatedPhysicalRootBudget_nonneg B U b S c).trans hbudget) hτ hξ1 N hN hτ1 hsize
    (allocatedPhysicalCubeRoot B U b S c x y) (allocatedPhysicalCubeDirections B U b S x y)
    (fun s => (allocatedPhysicalCube_supported_site_sum B U b S c x y hx hy s).trans hbudget) test z

include hx hy hbudget hτ hξ1 hN hτ1 hsize in
theorem allocatedPhysicalCube_supported_testExtension_mean
    (law : FiniteProbabilityWeights (trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0 (narrowTrimmedSpatialWidths (G := G)
        (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) 1))
    (test : Finset (Fin dim) → (X → ℝ) → ℂ) :
    law.complexMean (fun z => physicalCubeSiteTest (fun s => integerBoxTestExtension N (test s))
        (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S c x y)
          (allocatedPhysicalCubeDirections B U b S x y) z.1.val z.2.val)) =
      law.complexMean (fun z => physicalCubeSiteTest test
        (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S c x y)
          (allocatedPhysicalCubeDirections B U b S x y) z.1.val z.2.val)) := by
  apply congrArg law.complexMean
  funext z
  exact allocatedPhysicalCube_supported_testExtension B U b S c x y hx hy hbudget hτ hξ1 N hN hτ1 hsize test z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "refcols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y₀
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

theorem allocatedNarrowTrimmed_kernel_error (selection : α ↪ G) {M : ℕ}
    {X : Type*} (N q : X → ℕ) (d : X) (hN : ∀ a, 0 < N a) (hq : ∀ a, 0 < q a)
    {W τ κ C₀ ρ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsize : 8 * (1 + W) * (q d : ℝ) * ρ ≤ (ξ * τ) * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ) :
    let H := trimmedSpatialRootScale τ N q d
    let T := trimmedSpatialSlopeScale W τ N q d
    let hs := trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    ∀ v, |(∏ i, physicalSpatialOutputScale α H T S.value i) *
        (smoothMatrixImagePMF (physicalCubeCoefficient root dirs)
          (fun k => residueProfileWidth q V (k, d))
          (fun k => residueProfileWidth_pos q V hq hV (k, d)) v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection) cols)
        (physicalSpatialOutputScale α H T S.value)
        (anisotropicSpatialKernelDensity selection ker (scalarCubeDifferenceMatrix x) hp H T S.value
          hs.1 hs.2 (Nat.cast_pos.mpr S.positive)) v| ≤
      anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ := by
  intro H T hs V hV hp
  have hWT : W * T ≤ H := by
    change W * T ≤ trimmedSpatialRootScale τ N q d
    rw [trimmedSpatial_scale_ratio hW]
    exact mul_le_mul_of_nonneg_right (by linarith) hs.2.le
  have hscale := narrowTrimmedSpatial_scale_lower hW hτ hξ1 hρ.le N q d (hN d) (hq d) hsize
  have h := allocatedPhysicalCube_narrow_error B U basis S c x y selection hs.1 hs.2 hκ hρ
    hx hC₀ hLC hbudget hWT hWC hξ hξ1 hscale.1 hscale.2.2 hmesh
  simpa only [H, T, V, ← narrowTrimmedSpatial_residue_scale W τ ξ N q d] using h

theorem allocatedNarrowTrimmed_shifted_vector_site_error (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ δ b r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ (ξ * τ) * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (residue : Option vars × X → ℤ) (hresidue : ∀ k d, |(residue (k,d) : ℝ)| ≤ q d)
    (hCR : ∀ d, integerResidueMatrix cols (q d * modulus) =
      integerResidueMatrix refcols (q d * modulus))
    (hδ : 0 ≤ δ)
    (hmove : ∀ d i, (∑ j, |((cols i j - refcols i j : ℤ) : ℝ)|) ≤
      δ * trimmedSpatialRootScale τ N q d)
    (hb : 0 < b) (hr : 0 < r) (v : X → (Unit ⊕ α) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / trimmedSpatialRootScale τ N q d| ≤ b) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let hpivot := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hpivot W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let E := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ
    let G₀ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
    let shift := physicalResidueOffsetShift root (allocatedPhysicalCubeRoot B U basis S c x y₀)
      dirs (allocatedPhysicalCubeDirections B U basis S x y₀) residue q
    let E' := E + G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * δ
    ‖(((∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i) *
        (((smoothProductPMF Q hQ).map (fun z d => physicalCubeCoefficient root dirs *ᵥ
          (fun k => z (k, d)))) (v - shift)).toReal : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix refcols modulus))) modulus f (H d) b r (v d)‖ ≤
      Fintype.card X * (E' + 4 * G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
        (1 + G₀ * anisotropicSpatialDensityCap selection κ + E') ^ Fintype.card X := by
  classical
  intro H T V hV Q hQ hpivot f E G₀ shift E'
  have hH (d) : 0 < H d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1
  have hT (d) : 0 < T d := (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2
  have hroot (g : G) : |(ker g : ℝ)| ≤ 1 + W := by
    have h : |(ker g : ℝ)| ≤ W :=
      (allocatedPhysicalCube_root_budget B U basis S c x y (.inl g)).trans hbudget
    linarith
  have hD (i : α) (g : G) : |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value :=
    allocatedPhysicalCube_directions_bound B U basis S x y i (.inl g)
  have hminor : κ ≤ |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) /
      (S.value : ℝ))).det| := by
    change κ ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hE : 0 ≤ E := anisotropicSpatialError_nonneg selection _ M hκ.le
    (zero_le_one.trans hC₀) hρ.le hξ.le
  have hpoint (d) := allocatedNarrowTrimmed_kernel_error B U basis S c x y selection N q d hN hq
    hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ hξ1 (hsize d) hmesh
  have hshift : shift = fun d => residueMatrixShift cols refcols (q d)
      (fun j => residue (some (Sum.inr j), d)) :=
    allocatedPhysicalResidue_shift_principal B U basis S c x y y₀ residue q
  rw [hshift, smoothProductPMF_matrix_image_scaled]
  exact canonicalVectorSpatialSiteApprox_shift_error selection ker (scalarCubeDifferenceMatrix x) hpivot
    (fun _ => cols) (fun _ => refcols) H T hH hT hW (Nat.cast_pos.mpr S.positive)
    (by exact_mod_cast S.positive) hκ (fun d => trimmedSpatial_scale_ratio hW N q d)
    hroot hD hminor modulus hperiod q hq (fun d j => residue (some (Sum.inr j), d))
    (fun d j => hresidue (some (Sum.inr j)) d) hCR hδ hmove _ hE hb hr hpoint v hv

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule
open scoped BigOperators Classical Matrix

theorem allocatedReferenceSpatialProxy_bound {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    {M : ℕ} (hM : 0 < M) (selection : α ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (period : ℕ) [NeZero period]
    (hperiod : integerScalarLattice (Unit ⊕ α) (period : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    {X : Type*} [Fintype X] (H : X → ℝ) (hH : ∀ t, 0 < H t)
    {W : ℝ} (hW : 0 ≤ W) (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    {mesh : ℝ} (hmesh : 0 < mesh) :
    let ker := fun g => (0 : ℤ) + (x g none : ℤ)
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
      hW (Nat.cast_pos.mpr S.positive)
    ∀ w ∈ spatialWindow H 4,
      ‖∏ t, spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix (principalSpatialColumns (fun _ => (0 : ℤ)) id y) period)))
        period f (H t) 4 mesh (w t)‖ ≤
      ((period : ℝ) ^ Fintype.card (Unit ⊕ α) *
        anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X := by
  intro ker hp f w hw
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hC := anisotropicSpatialDensityCap_nonneg selection hκ.le
  have hroot (g : G) : |(ker g : ℝ)| ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U b S (fun _ => 0) x y (.inl g)).trans hbudget
    change |(ker g : ℝ)| ≤ W at h
    linarith
  have hD (i : α) (g : G) : |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value :=
    allocatedPhysicalCube_directions_bound B U b S x y i (.inl g)
  have hminor : 1 / (M : ℝ) ≤
      |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) / (S.value : ℝ))).det| := by
    change 1 / (M : ℝ) ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hf := (canonicalSpatialSiteDensity_bounds selection ker (scalarCubeDifferenceMatrix x) hp
    hW (Nat.cast_pos.mpr S.positive) (by exact_mod_cast S.positive) hκ hroot hD hminor).1
  apply residueSpatialSite_norm_le _ _ period hperiod (fun _ => f) H (by norm_num) hmesh hC
    (fun _ => hf) (fun _ => integerResidueMatrix (principalSpatialColumns (fun _ => (0 : ℤ)) id y) period) w
  exact (mem_spatialWindow_scaled_iff H hH 4 w).mp hw

end Erdos3.VectorPolynomial

end

end OAI
