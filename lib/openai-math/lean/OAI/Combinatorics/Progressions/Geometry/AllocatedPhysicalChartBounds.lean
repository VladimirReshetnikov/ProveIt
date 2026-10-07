import OAI.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedPhysicalRootAllowance (c : LayerSamplerVariables G I n B → ℤ) : ℝ :=
  1 + ∑ k, |(c k : ℝ)| / layerSamplerBox B U b S k

theorem allocatedPhysicalRootAllowance_one_le (c : LayerSamplerVariables G I n B → ℤ) :
    1 ≤ allocatedPhysicalRootAllowance B U b S c := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg (fun k _ => div_nonneg (abs_nonneg _) (zero_le_one.trans (layerSamplerBox_one_le B U b S k)))

theorem allocatedPhysicalRootAllowance_zero :
    allocatedPhysicalRootAllowance B U b S (fun _ => 0) = 1 := by
  simp [allocatedPhysicalRootAllowance]

theorem allocatedPhysicalRootAllowance_le (c : LayerSamplerVariables G I n B → ℤ) :
    allocatedPhysicalRootAllowance B U b S c ≤ 1 + ∑ k, |(c k : ℝ)| := by
  unfold allocatedPhysicalRootAllowance
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k _
  exact div_le_self (abs_nonneg _) (layerSamplerBox_one_le B U b S k)

theorem allocatedPhysicalRootAllowance_le_box (c : LayerSamplerVariables G I n B → ℤ)
    (hc : ∀ k, |(c k : ℝ)| ≤ layerSamplerBox B U b S k) :
    allocatedPhysicalRootAllowance B U b S c ≤
      1 + Fintype.card (LayerSamplerVariables G I n B) := by
  unfold allocatedPhysicalRootAllowance
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _k : LayerSamplerVariables G I n B, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      exact (div_le_one (lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k))).mpr (hc k)
    _ = _ := by simp

variable {α : Type*} (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))

theorem allocatedPhysicalCube_tuple_coordinate_bound (a : Option α) (k : LayerSamplerVariables G I n B) :
    |((Sum.elim (fun g => (x g a : ℤ)) (fun j => (y j a : ℤ)) k : ℤ) : ℝ)| ≤ layerSamplerBox B U b S k := by
  cases k with
  | inl g =>
    have hx := Finset.mem_Ico.mp (x g a).property
    change |((x g a : ℤ) : ℝ)| ≤ (S.value : ℝ)
    exact_mod_cast abs_le.mpr ⟨hx.1, hx.2.le⟩
  | inr j =>
    have hy := Finset.mem_Ico.mp (y j a).property
    change |((y j a : ℤ) : ℝ)| ≤ (allocatedPrincipalSides B U b S j : ℝ)
    exact_mod_cast abs_le.mpr ⟨hy.1, hy.2.le⟩

theorem allocatedPhysicalCube_directions_normalized (i : α) (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeDirections B U b S x y i k : ℝ) / layerSamplerBox B U b S k| ≤ 1 := by
  have hT : 0 < layerSamplerBox B U b S k := lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  rw [abs_div, abs_of_pos hT, div_le_one hT]
  exact allocatedPhysicalCube_tuple_coordinate_bound B U b S x y (some i) k

theorem allocatedPhysicalCube_root_normalized (c : LayerSamplerVariables G I n B → ℤ)
    (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U b S c x y k : ℝ) / layerSamplerBox B U b S k| ≤
      allocatedPhysicalRootAllowance B U b S c := by
  have hT : 0 < layerSamplerBox B U b S k := lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  have hsum : |(c k : ℝ)| / layerSamplerBox B U b S k ≤
      ∑ k, |(c k : ℝ)| / layerSamplerBox B U b S k :=
    Finset.single_le_sum (fun v _ => div_nonneg (abs_nonneg (c v : ℝ))
      (zero_le_one.trans (layerSamplerBox_one_le B U b S v))) (Finset.mem_univ k)
  have hx := allocatedPhysicalCube_tuple_coordinate_bound B U b S x y none k
  rw [abs_div, abs_of_pos hT]
  have hr : |(allocatedPhysicalCubeRoot B U b S c x y k : ℝ)| ≤
      |(c k : ℝ)| + layerSamplerBox B U b S k := by
    unfold allocatedPhysicalCubeRoot
    rw [Int.cast_add]
    exact (abs_add_le _ _).trans (add_le_add le_rfl hx)
  calc
    _ ≤ (|(c k : ℝ)| + layerSamplerBox B U b S k) / layerSamplerBox B U b S k :=
      div_le_div_of_nonneg_right hr hT.le
    _ = |(c k : ℝ)| / layerSamplerBox B U b S k + 1 := by rw [add_div, div_self hT.ne']
    _ ≤ allocatedPhysicalRootAllowance B U b S c := by
      dsimp [allocatedPhysicalRootAllowance]
      linarith

end Erdos3.VectorPolynomial

end

end OAI
