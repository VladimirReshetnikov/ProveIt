import OAI.Combinatorics.Progressions.Probability.AllocatedAnisotropicSpatialLaw
import OAI.Combinatorics.Progressions.Probability.AnisotropicCanonicalDensity
import OAI.Combinatorics.Progressions.Probability.CenteredPhysicalProductLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

noncomputable def allocatedPhysicalRootBudget : ℝ :=
  (∑ k, |(c k : ℝ)|) + Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ)

theorem allocatedPhysicalRootBudget_nonneg : 0 ≤ allocatedPhysicalRootBudget B U basis S c := by
  unfold allocatedPhysicalRootBudget
  positivity

noncomputable def allocatedPhysicalEntryBudget : ℝ :=
  1 + allocatedPhysicalRootBudget B U basis S c + (S.value : ℝ)

theorem allocatedPhysicalEntryBudget_one_le : 1 ≤ allocatedPhysicalEntryBudget B U basis S c := by
  have h := allocatedPhysicalRootBudget_nonneg B U basis S c
  unfold allocatedPhysicalEntryBudget
  linarith [Nat.cast_nonneg (α := ℝ) S.value]

omit [Fintype α] in
theorem allocatedPhysicalCube_directions_bound (i : α) (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤ S.value := by
  cases k with
  | inl g =>
    have hx := Finset.mem_Ico.mp (x g (some i)).property
    change |((x g (some i) : ℤ) : ℝ)| ≤ S.value
    exact_mod_cast abs_le.mpr ⟨hx.1, hx.2.le⟩
  | inr j =>
    have hy := Finset.mem_Ico.mp (y j (some i)).property
    have hbound : |(y j (some i) : ℤ)| ≤ allocatedPrincipalSides B U basis S j :=
      abs_le.mpr ⟨hy.1, hy.2.le⟩
    change |((y j (some i) : ℤ) : ℝ)| ≤ S.value
    exact (by exact_mod_cast hbound : |((y j (some i) : ℤ) : ℝ)| ≤
      allocatedPrincipalSides B U basis S j).trans
        (Nat.cast_le.mpr (allocatedPrincipalSides_le_scale B U basis S j))

omit [Fintype α] in
theorem allocatedPhysicalCube_root_bound (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤ |(c k : ℝ)| + S.value := by
  have hv : |((Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) k : ℤ) : ℝ)| ≤ S.value := by
    cases k with
    | inl g =>
      have hx := Finset.mem_Ico.mp (x g none).property
      change |((x g none : ℤ) : ℝ)| ≤ S.value
      exact_mod_cast abs_le.mpr ⟨hx.1, hx.2.le⟩
    | inr j =>
      have hy := Finset.mem_Ico.mp (y j none).property
      have hbound : |(y j none : ℤ)| ≤ allocatedPrincipalSides B U basis S j :=
        abs_le.mpr ⟨hy.1, hy.2.le⟩
      exact (by exact_mod_cast hbound : |((y j none : ℤ) : ℝ)| ≤
        allocatedPrincipalSides B U basis S j).trans
          (Nat.cast_le.mpr (allocatedPrincipalSides_le_scale B U basis S j))
  unfold allocatedPhysicalCubeRoot
  push_cast
  exact (abs_add_le _ _).trans (add_le_add le_rfl hv)

omit [Fintype α] in
theorem allocatedPhysicalCube_root_sum :
    (∑ k, |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)|) ≤
      allocatedPhysicalRootBudget B U basis S c := by
  calc
    _ ≤ ∑ k, (|(c k : ℝ)| + (S.value : ℝ)) :=
      Finset.sum_le_sum (fun k _ => allocatedPhysicalCube_root_bound B U basis S c x y k)
    _ = _ := by simp [allocatedPhysicalRootBudget, Finset.sum_add_distrib]

omit [Fintype α] in
theorem allocatedPhysicalCube_root_budget (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤
      allocatedPhysicalRootBudget B U basis S c :=
  (Finset.single_le_sum (fun j _ => abs_nonneg (allocatedPhysicalCubeRoot B U basis S c x y j : ℝ))
    (Finset.mem_univ k)).trans (allocatedPhysicalCube_root_sum B U basis S c x y)

omit [Fintype α] in
theorem allocatedPhysicalCube_root_entry_bound (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeRoot B U basis S c x y k : ℝ)| ≤ allocatedPhysicalEntryBudget B U basis S c := by
  apply (allocatedPhysicalCube_root_budget B U basis S c x y k).trans
  unfold allocatedPhysicalEntryBudget
  linarith [Nat.cast_nonneg (α := ℝ) S.value]

omit [Fintype α] in
theorem allocatedPhysicalCube_direction_entry_bound (i : α) (k : LayerSamplerVariables G I n B) :
    |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)| ≤ allocatedPhysicalEntryBudget B U basis S c := by
  apply (allocatedPhysicalCube_directions_bound B U basis S x y i k).trans
  have h := allocatedPhysicalRootBudget_nonneg B U basis S c
  unfold allocatedPhysicalEntryBudget
  linarith

omit [Fintype α] in
theorem allocatedPhysicalCube_kernel_range :
    (scalarCubeDifferenceMatrix x).mulVecLin.range ≤
      (allocatedPhysicalCubeDirections B U basis S x y).mulVecLin.range := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro v ⟨g, rfl⟩
  exact ⟨Sum.inl g, rfl⟩

theorem allocatedPhysicalCube_period {M : ℕ}
    (hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M) :
    HasBoundedScalarPeriod (allocatedPhysicalCubeDirections B U basis S x y).mulVecLin.range M := by
  obtain ⟨q, hq, hqM, hqrange⟩ := hperiod
  exact ⟨q, hq, hqM, hqrange.trans (allocatedPhysicalCube_kernel_range B U basis S x y)⟩

variable [DecidableEq α] [DecidableEq G]

theorem allocatedPhysicalCube_minor (selection : α ↪ G) :
    (Matrix.of (fun i j =>
      (allocatedPhysicalCubeDirections B U basis S x y i
        ((selection.trans Function.Embedding.inl) j) : ℝ) / (S.value : ℝ))).det =
      normalizedScalarCubeMinor selection x := by
  change (normalizedScalarCubePivot selection x).det = _
  exact normalizedScalarCubePivot_det selection x

theorem allocatedPhysicalCube_good_kernel (selection : α ↪ G) {κ : ℝ} {M : ℕ}
    (hx : GoodScalarKernelTuple selection κ M x) :
    κ ≤ |(Matrix.of (fun i j =>
      (allocatedPhysicalCubeDirections B U basis S x y i
        ((selection.trans Function.Embedding.inl) j) : ℝ) / (S.value : ℝ))).det| ∧
      HasBoundedScalarPeriod (allocatedPhysicalCubeDirections B U basis S x y).mulVecLin.range M := by
  rw [allocatedPhysicalCube_minor]
  exact ⟨hx.1.le, allocatedPhysicalCube_period B U basis S x y hx.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators NNReal

theorem anisotropicSpatialError_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (N : Type*) [Fintype N] (B : ℕ) {κ C ρ ξ : ℝ}
    (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hξ : 0 ≤ ξ) :
    0 ≤ anisotropicSpatialError s N B κ C ρ ξ := by
  unfold anisotropicSpatialError normalizedFiberErrorConstant integerFiberErrorConstant
    anisotropicSpatialDetAllowance physicalSpatialInverseBound spatialKernelErrorConstant
  positivity

theorem canonicalVectorSpatialSiteApprox_error {D I J N : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype N]
    (s : I ↪ J) (root : J → ℤ) (M : Matrix I J ℤ)
    (hpivot : (selectedSpatialPivot root M s).det ≠ 0)
    (C : D → Matrix (Unit ⊕ I) N ℤ) (H T : D → ℝ)
    {W L κ E b r : ℝ} (hH : ∀ d, 0 < H d) (hT : ∀ d, 0 < T d)
    (hW : 0 ≤ W) (hL : 0 < L) (hL1 : 1 ≤ L) (hκ : 0 < κ)
    (hscale : ∀ d, H d = (1 + W) * T d)
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + W) (hM : ∀ i j, |(M i j : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (M i (s j) : ℝ) / L)).det|)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root M s) (selectedSpatialFreeColumns root M s))
    (mass : D → ((Unit ⊕ I) → ℤ) → ℝ) (hE : 0 ≤ E) (hb : 0 < b) (hr : 0 < r)
    (hmass : ∀ d v, |mass d v -
      maskedIntegerImageDensity (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (C d))
        (physicalSpatialOutputScale I (H d) (T d) L)
        (anisotropicSpatialKernelDensity s root M hpivot (H d) (T d) L (hH d) (hT d) hL) v| ≤ E)
    (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ b) :
    let G := (m : ℝ) ^ Fintype.card (Unit ⊕ I)
    let f := canonicalSpatialSiteDensity s root M hpivot W L hW hL
    ‖((∏ d, mass d (v d) : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (liftResidueMatrix (integerResidueMatrix (C d) m)))
        m f (H d) b r (v d)‖ ≤
      Fintype.card D * (E + 4 * G * (anisotropicSpatialDensityLip s κ * (1 + W)) * r) *
        (1 + G * anisotropicSpatialDensityCap s κ + E) ^ Fintype.card D := by
  intro G f
  have hpfull (d : D) : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (C d)) := by
    rw [pivotFullImage_split]
    exact hp.trans le_sup_left
  have hi (d : D) :
      ((pivotFullImage (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (C d))).toAddSubgroup.index : ℝ) ≤ G := by
    dsimp only [G]
    exact_mod_cast residueLatticeImage_index_le _ m (hpfull d)
  have hreg := canonicalSpatialSiteDensity_bounds s root M hpivot hW hL hL1 hκ hroot hM hminor
  have he (d : D) (w : (Unit ⊕ I) → ℤ) : |mass d w -
      maskedIntegerImageDensity (selectedSpatialPivot root M s)
        (Matrix.fromCols (selectedSpatialFreeColumns root M s) (C d)) (fun _ => H d) f w| ≤ E := by
    have h := hmass d w
    rw [anisotropicSpatial_mask_canonical s root M hpivot _ (hH d) (hT d) hW hL (hscale d)] at h
    exact h
  have h := vectorSpatialSiteApprox_error _ _ m hpfull (fun _ => f) (fun _ => hreg.2)
    H mass (by positivity) (anisotropicSpatialDensityCap_nonneg s hκ.le) hE hb hr hi
    (fun _ => hreg.1) he v hv
  have hid (d : D) := congrFun (spatialSiteApprox_eq_residue (selectedSpatialPivot root M s)
    (selectedSpatialFreeColumns root M s) (C d) m hp f (H d) b r) (v d)
  simpa only [hid, NNReal.coe_mul,
    Real.coe_toNNReal _ (anisotropicSpatialDensityLip_nonneg s hκ.le),
    Real.coe_toNNReal _ (by linarith : 0 ≤ 1 + W)] using h

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

omit [Fintype α] in
theorem allocatedPhysicalCube_direction_sum (i : α) :
    (∑ k, |(allocatedPhysicalCubeDirections B U basis S x y i k : ℝ)|) ≤
      allocatedPhysicalRootBudget B U basis S c := by
  calc
    _ ≤ ∑ _k : LayerSamplerVariables G I n B, (S.value : ℝ) :=
      Finset.sum_le_sum (fun k _ => allocatedPhysicalCube_directions_bound B U basis S x y i k)
    _ = Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) := by simp
    _ ≤ _ := le_add_of_nonneg_left (Finset.sum_nonneg (fun k _ => abs_nonneg (c k : ℝ)))

theorem allocatedTrimmedSpatial_window_bound {X : Type*} [Fintype X]
    (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (v : X → (Unit ⊕ α) → ℤ)
    (hv : v ∈ centeredPhysicalCubeWindow (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (residueProfileWidth q (trimmedSpatialWidths (K := LayerSamplerVariables G I n B) W τ N))) :
    ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / trimmedSpatialRootScale τ N q d| ≤ 3 := by
  apply centeredPhysicalCubeWindow_star_bound _ _ _ _ (fun d => trimmedSpatialSlopeScale W τ N q d)
    hW (fun d => (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).1)
    (fun d => (trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)).2.le)
    (fun d => trimmedSpatial_scale_ratio hW N q d)
    (fun d => trimmedSpatial_residue_scale W τ N q d)
    ((allocatedPhysicalCube_root_sum B U basis S c x y).trans hbudget)
    (fun i => (allocatedPhysicalCube_direction_sum B U basis S c x y i).trans hbudget) v hv

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

theorem allocatedParameterSite_bound (t : integerBox sides) (k : LayerSamplerVariables G I n B) :
    |(t.val k : ℝ)| ≤ S.value := by
  have ht := (mem_integerBox sides t.val).mp t.property k
  have hk : sides k ≤ S.value := by
    cases k with
    | inl g => exact le_rfl
    | inr j => exact allocatedPrincipalSides_le_scale B U b S j
  have hk' : (sides k : ℤ) ≤ (S.value : ℤ) := by exact_mod_cast hk
  have ht' : |t.val k| ≤ (S.value : ℤ) := by
    rw [abs_of_nonneg ht.1]
    exact ht.2.le.trans hk'
  exact_mod_cast ht'

theorem allocatedParameterSite_sum_bound (t : integerBox sides) :
    (∑ k, |(t.val k : ℝ)|) ≤ allocatedPhysicalRootBudget B U b S (fun _ => 0) := by
  calc
    _ ≤ ∑ _k : LayerSamplerVariables G I n B, (S.value : ℝ) :=
      Finset.sum_le_sum (fun k _ => allocatedParameterSite_bound B U b S t k)
    _ = _ := by simp [allocatedPhysicalRootBudget]

theorem allocatedParameterBox_nonempty : (integerBox sides).Nonempty := by
  have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
    cases k with
    | inl g => exact S.positive
    | inr j => exact allocatedPrincipalSides_pos B U b S j
  let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
  exact integerBox_nonempty sides

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

noncomputable def allocatedPrimitiveRootRatio (p : ℝ) : ℝ≥0 := Real.toNNReal (p + 1)

theorem allocatedPrimitiveRootRatio_bounds {p : ℝ} (hp : 0 ≤ p) :
    (allocatedPrimitiveRootRatio p : ℝ) = p + 1 ∧
      1 ≤ allocatedPrimitiveRootRatio p ∧
      (allocatedPrimitiveRootRatio p : ℝ) ≤ Real.exp (p + 1) := by
  have heq : (allocatedPrimitiveRootRatio p : ℝ) = p + 1 :=
    Real.coe_toNNReal _ (by linarith)
  refine ⟨heq, ?_, ?_⟩
  · exact_mod_cast (show (1 : ℝ) ≤ allocatedPrimitiveRootRatio p by rw [heq]; linarith)
  · rw [heq]
    linarith [Real.add_one_le_exp (p + 1)]

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedPhysicalRootBudget_zero :
    allocatedPhysicalRootBudget B U b S (fun _ => 0) =
      Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) := by
  simp only [allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add]

theorem allocatedPhysicalRootBudget_zero_ratio {p : ℝ} (hp : 0 ≤ p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p) :
    (1 + allocatedPhysicalRootBudget B U b S (fun _ => 0)) / (S.value : ℝ) ≤
      allocatedPrimitiveRootRatio p := by
  have hS : (0 : ℝ) < S.value := Nat.cast_pos.mpr S.positive
  have hS1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  rw [allocatedPhysicalRootBudget_zero, (allocatedPrimitiveRootRatio_bounds hp).1,
    add_div, mul_div_cancel_right₀ _ hS.ne']
  have hinv : 1 / (S.value : ℝ) ≤ 1 := (div_le_one hS).mpr hS1
  linarith

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
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

theorem allocatedTrimmedSpatial_kernel_error (selection : α ↪ G) {M : ℕ}
    {X : Type*} (N q : X → ℕ) (d : X) (hN : ∀ a, 0 < N a) (hq : ∀ a, 0 < q a)
    {W τ κ C₀ ρ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hprincipalRoot : ∀ j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) ≤
      ξ * (1 + W))
    (hprincipalDir : ∀ j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) ≤
      ξ * S.value)
    (hsize : 8 * (1 + W) * (q d : ℝ) * ρ ≤ τ * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ) :
    let H := trimmedSpatialRootScale τ N q d
    let T := trimmedSpatialSlopeScale W τ N q d
    let hs := trimmedSpatial_scales_pos hW hτ N q d (hN d) (hq d)
    let hV := trimmedSpatialWidths_pos (K := vars) hW hτ N hN
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    ∀ v, |(∏ i, physicalSpatialOutputScale α H T S.value i) *
        (smoothMatrixImagePMF (physicalCubeCoefficient root dirs)
          (fun k => residueProfileWidth q (trimmedSpatialWidths (K := vars) W τ N) (k, d))
          (fun k => residueProfileWidth_pos q _ hq hV (k, d)) v).toReal -
      maskedIntegerImageDensity (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection) cols)
        (physicalSpatialOutputScale α H T S.value)
        (anisotropicSpatialKernelDensity selection ker (scalarCubeDifferenceMatrix x) hp H T S.value
          hs.1 hs.2 (Nat.cast_pos.mpr S.positive)) v| ≤
      anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ := by
  intro H T hs hV hp
  have hr (g : G) : |(ker g : ℝ)| * T ≤ H :=
    trimmedSpatial_root_control hW hτ N q d (hN d) (hq d) root
      ((allocatedPhysicalCube_root_sum B U basis S c x y).trans hbudget) (.inl g)
  have hrC (g : G) : |(ker g : ℝ)| ≤ C₀ :=
    ((allocatedPhysicalCube_root_budget B U basis S c x y (.inl g)).trans hbudget).trans hWC
  have hwidth : ∀ i j,
      ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) * T ≤
        ξ * physicalSpatialOutputScale α H T S.value i := by
    rintro (i | i) j
    · change _ ≤ ξ * H
      have he : H = (1 + W) * T := trimmedSpatial_scale_ratio hW N q d
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_right (hprincipalRoot j) hs.2.le]
    · change _ ≤ ξ * ((S.value : ℝ) * T)
      nlinarith [mul_le_mul_of_nonneg_right (hprincipalDir j) hs.2.le]
  have hscales := trimmedSpatial_scale_lower hW hρ.le N q d (hq d) hsize
  have h := allocatedPhysicalCube_anisotropic_error B U basis S c x y selection hs.1 hs.2 hκ hρ
    hx hC₀ hLC hr hrC hξ0 hξ1 hwidth hscales.1 hscales.2 hmesh
  simpa only [H, T, ← trimmedSpatial_residue_scale (K := vars) W τ N q d] using h

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
variable (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))

local notation "vars" => LayerSamplerVariables G I n B
local notation "cols" => principalSpatialColumns (fun j => c (Sum.inr j)) id y
local notation "ker" => (fun g => c (Sum.inl g) + (x g none : ℤ))
local notation "root" => allocatedPhysicalCubeRoot B U basis S c x y
local notation "dirs" => allocatedPhysicalCubeDirections B U basis S x y

theorem allocatedTrimmedSpatial_vector_site_error (selection : α ↪ G) {M : ℕ}
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ d, 0 < N d) (hq : ∀ d, 0 < q d)
    {W τ κ C₀ ρ ξ b r : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hx : GoodScalarKernelTuple selection κ M x)
    (hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hprincipalRoot : ∀ j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) ≤
      ξ * (1 + W))
    (hprincipalDir : ∀ j, ((|c (.inr j)| : ℤ) + (allocatedPrincipalSides B U basis S j : ℤ) : ℝ) ≤
      ξ * S.value)
    (hsize : ∀ d, 8 * (1 + W) * (q d : ℝ) * ρ ≤ τ * (N d : ℝ))
    (hmesh : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (modulus : ℕ) [NeZero modulus]
    (hperiod : integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (hb : 0 < b) (hr : 0 < r) (v : X → (Unit ⊕ α) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / trimmedSpatialRootScale τ N q d| ≤ b) :
    let H := fun d => trimmedSpatialRootScale τ N q d
    let T := fun d => trimmedSpatialSlopeScale W τ N q d
    let V := trimmedSpatialWidths (K := vars) W τ N
    let hV := trimmedSpatialWidths_pos (K := vars) hW hτ N hN
    let Q := residueProfileWidth q V
    let hQ := residueProfileWidth_pos q V hq hV
    let hpivot := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hpivot W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let E := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M κ C₀ ρ ξ
    let G₀ := (modulus : ℝ) ^ Fintype.card (Unit ⊕ α)
    ‖(((∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) S.value i) *
        (((smoothProductPMF Q hQ).map (fun z d => physicalCubeCoefficient root dirs *ᵥ
          (fun k => z (k, d)))) v).toReal : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix cols modulus))) modulus f (H d) b r (v d)‖ ≤
      Fintype.card X * (E + 4 * G₀ * (anisotropicSpatialDensityLip selection κ * (1 + W)) * r) *
        (1 + G₀ * anisotropicSpatialDensityCap selection κ + E) ^ Fintype.card X := by
  classical
  intro H T V hV Q hQ hpivot f E G₀
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
    (zero_le_one.trans hC₀) hρ.le hξ0
  have hpoint (d) := allocatedTrimmedSpatial_kernel_error B U basis S c x y selection N q d hN hq
    hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ0 hξ1 hprincipalRoot hprincipalDir (hsize d) hmesh
  rw [smoothProductPMF_matrix_image_scaled]
  exact canonicalVectorSpatialSiteApprox_error selection ker (scalarCubeDifferenceMatrix x) hpivot
    (fun _ => cols) H T hH hT hW (Nat.cast_pos.mpr S.positive)
    (by exact_mod_cast S.positive) hκ (fun d => trimmedSpatial_scale_ratio hW N q d)
    hroot hD hminor modulus hperiod _ hE hb hr hpoint v hv

end Erdos3.VectorPolynomial

end

end OAI
