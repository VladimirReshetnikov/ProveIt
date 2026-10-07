import OAI.Combinatorics.Progressions.Estimates.AllocatedRefinedWholeReference

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule BooleanCubeKernel
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ)
variable {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)

noncomputable def allocatedResidueSpatialKernel
    (r : labels) (v : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
  let ker := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  ∏ t, spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
    (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
      (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r)))
    modulus f (H t) 4 mesh (v t)

theorem allocatedResidueSpatialKernel_norm_le
    (hH : ∀ t, 0 < H t) (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (r : labels) (v : X → (Unit ⊕ Fin dim) → ℤ) (hv : v ∈ spatialWindow H 4) :
    ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r v‖ ≤
      ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
        anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X := by
  let ker := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  obtain ⟨y, _hy⟩ := (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    sides (allocatedPrincipalSides_pos B U b S)).exists_weight_pos
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hC := anisotropicSpatialDensityCap_nonneg selection hκ.le
  have hroot (g : G) : |(ker g : ℝ)| ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U b S (fun _ => 0) x y (.inl g)).trans hbudget
    change |(ker g : ℝ)| ≤ W at h
    linarith
  have hD (i : Fin dim) (g : G) : |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value :=
    allocatedPhysicalCube_directions_bound B U b S x y i (.inl g)
  have hminor : 1 / (M : ℝ) ≤
      |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) / (S.value : ℝ))).det| := by
    change 1 / (M : ℝ) ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hf := (canonicalSpatialSiteDensity_bounds selection ker (scalarCubeDifferenceMatrix x) hp
    hW (Nat.cast_pos.mpr S.positive) (by exact_mod_cast S.positive) hκ hroot hD hminor).1
  exact residueSpatialSite_norm_le _ _ modulus hperiod (fun _ : X => f) H (by norm_num) hmesh hC
    (fun _ => hf) (fun _ => principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r) v
    ((mem_spatialWindow_scaled_iff H hH 4 v).mp hv)

noncomputable def allocatedResidueSpatialWindowWeight
    (r : labels) (v : X → (Unit ⊕ Fin dim) → ℤ) : ℂ :=
  if v ∈ spatialWindow H 4 then
    allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r v
  else 0

theorem allocatedResidueSpatialWindowWeight_norm_le
    (hH : ∀ t, 0 < H t) (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hmesh : 0 < mesh)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection))
    (r : labels) (v : X → (Unit ⊕ Fin dim) → ℤ) :
    ‖allocatedResidueSpatialWindowWeight B U b S x X hM selection hx modulus H hW mesh r v‖ ≤
      ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
        anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X := by
  unfold allocatedResidueSpatialWindowWeight
  split_ifs with hv
  · exact allocatedResidueSpatialKernel_norm_le B U b S x X hM selection hx modulus H hW mesh
      hH hbudget hmesh hperiod r v hv
  · rw [norm_zero]
    exact pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus) _)
      (anisotropicSpatialDensityCap_nonneg selection (one_div_nonneg.mpr (Nat.cast_nonneg M)))) _

variable (q : X → ℕ) {τ : ℝ}
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedRefinedSpatialKernel_residue
    (N : X → ℕ)
    (u : PrincipalAxisTuples (α := Fin dim) grid sides)
    (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) :
    allocatedRefinedSpatialKernel (τ := τ) B U b S x X hM selection hx modulus q reference N hW mesh u r =
      allocatedResidueSpatialKernel B U b S x X hM selection hx modulus (trimmedSpatialRootScale τ N q) hW mesh
        (principalResidueLabel modulus (principalAxisJoin grid u (reference u r))) := by
  funext v
  simp only [allocatedRefinedSpatialKernel, allocatedResidueSpatialKernel, principalSpatialColumns_residue]

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedRefinedSpatialKernel_whole_residue
    (N : X → ℕ)
    (href : ∀ u r, principalResidueLabel (residueRefinedPeriod modulus q) (reference u r) = r)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides) :
    allocatedRefinedSpatialKernel (τ := τ) B U b S x X hM selection hx modulus q reference N hW mesh
      (principalAxisRestrict grid y)
      (principalResidueLabel (residueRefinedPeriod modulus q) (principalAxisRestrict (fun a => ¬grid a) y)) =
      allocatedResidueSpatialKernel B U b S x X hM selection hx modulus (trimmedSpatialRootScale τ N q) hW mesh
        (principalResidueLabel modulus y) := by
  rw [allocatedRefinedSpatialKernel_residue]
  have hlabel := principalResidueLabel_eq_of_dvd
    (reference (principalAxisRestrict grid y)
      (principalResidueLabel (residueRefinedPeriod modulus q) (principalAxisRestrict (fun a => ¬grid a) y)))
    (principalAxisRestrict (fun a => ¬grid a) y) ⟨∏ t, q t, rfl⟩
    (href (principalAxisRestrict grid y)
      (principalResidueLabel (residueRefinedPeriod modulus q) (principalAxisRestrict (fun a => ¬grid a) y)))
  rw [principalResidueLabel_join, hlabel, ← principalResidueLabel_join, principalAxisJoin_restrict]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical Matrix

noncomputable def allocatedSpatialCoefficientCap {G : Type*} [Fintype G] {dim : ℕ}
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) (M modulus : ℕ) (mesh : ℝ) : ℝ :=
  ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
    (intervalSiteCount 4 mesh : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
    ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ)))) ^ Fintype.card X

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

local notation "labels" => PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus
local notation "terms" => X → SpatialSiteLabel (Fin dim) modulus 4 mesh

noncomputable def allocatedSpatialExpansionCoefficient (r : labels) (t : terms) : ℂ :=
  let ker := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  ∏ z : X, spatialSiteCoefficient (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
    (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
      (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r)))
    modulus f 4 mesh (t z)

theorem allocatedResidueSpatialKernel_expansion (H : X → ℝ) (r : labels)
    (v : X → (Unit ⊕ Fin dim) → ℤ) :
    allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r v =
      ∑ t : terms, allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh r t *
        ∏ i, vectorResidueSiteWeight 4 mesh H (fun z => (t z).1 i) (fun z => (t z).2 i)
          (fun z => spatialStar (v z) i) := by
  unfold allocatedResidueSpatialKernel allocatedSpatialExpansionCoefficient
  exact vectorSpatialSiteExpansion _ _ modulus _ H 4 mesh v

theorem allocatedSpatialExpansionCoefficient_sum_le
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection)) (r : labels) :
    (∑ t : terms, ‖allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh r t‖) ≤
      allocatedSpatialCoefficientCap X selection M modulus mesh := by
  let ker := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  obtain ⟨y, _hy⟩ := (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).exists_weight_pos
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hroot (g : G) : |(ker g : ℝ)| ≤ 1 + W := by
    have h := (allocatedPhysicalCube_root_budget B U b S (fun _ => 0) x y (.inl g)).trans hbudget
    change |(ker g : ℝ)| ≤ W at h
    linarith
  have hD (i : Fin dim) (g : G) : |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value :=
    allocatedPhysicalCube_directions_bound B U b S x y i (.inl g)
  have hminor : 1 / (M : ℝ) ≤
      |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) / (S.value : ℝ))).det| := by
    change 1 / (M : ℝ) ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hf := (canonicalSpatialSiteDensity_bounds selection ker (scalarCubeDifferenceMatrix x) hp
    hW (Nat.cast_pos.mpr S.positive) (by exact_mod_cast S.positive) hκ hroot hD hminor).1
  let extra := Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
    (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r))
  have hfull : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection) extra := by
    dsimp only [extra]
    rw [pivotFullImage_split]
    exact hperiod.trans le_sup_left
  have hindex : ((pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
      extra).toAddSubgroup.index : ℝ) ≤ (modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) := by
    exact_mod_cast residueLatticeImage_index_le _ modulus hfull
  exact vectorSpatialSiteCoefficient_sum_bound _ (fun _ : X => extra) modulus (fun _ => f)
    4 mesh (fun _ => hindex) (fun _ => hf)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X]
variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ)

variable {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

theorem allocatedResidueSpatialKernel_remesh (Q : ℝ≥0) (hQ : 1 ≤ Q)
    (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
    (hroot : ∀ g, |((x g none : ℤ) : ℝ)| ≤ 1 + W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hH : ∀ t, 0 < H t) (hmesh : 0 < mesh) (coarse : ℝ) (hcoarse : 0 < coarse)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (hv : v ∈ spatialWindow H 4) :
    ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r v -
      allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW coarse r v‖ ≤
      Fintype.card X *
        (4 * (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (mesh + coarse)) *
        (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X := by
  let root := fun g => (0 : ℤ) + (x g none : ℤ)
  let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection
  let C := Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)
    (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r))
  have hκ : 0 < 1 / (M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x root hκ hx
  let f := canonicalSpatialSiteDensity selection root (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  have hL1 : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  have hroot' : ∀ g, |(root g : ℝ)| ≤ 1 + W := by
    intro g
    simpa only [root, zero_add] using hroot g
  have hD : ∀ i g, |(scalarCubeDifferenceMatrix x i g : ℝ)| ≤ S.value := by
    intro i g
    have hg := Finset.mem_Ico.mp (x g (some i)).property
    change |((x g (some i) : ℤ) : ℝ)| ≤ S.value
    exact_mod_cast abs_le.mpr ⟨hg.1, hg.2.le⟩
  have hminor : 1 / (M : ℝ) ≤
      |(Matrix.of (fun i j => (scalarCubeDifferenceMatrix x i (selection j) : ℝ) / (S.value : ℝ))).det| := by
    change 1 / (M : ℝ) ≤ |(normalizedScalarCubePivot selection x).det|
    rw [normalizedScalarCubePivot_det]
    exact hx.1.le
  have hf := canonicalSpatialSiteDensity_lipschitz_ratio selection root (scalarCubeDifferenceMatrix x)
    hp hW (Nat.cast_pos.mpr S.positive) hκ hroot' hD hminor hQ hratio
  have hcap := (canonicalSpatialSiteDensity_bounds selection root (scalarCubeDifferenceMatrix x)
    hp hW (Nat.cast_pos.mpr S.positive) hL1 hκ hroot' hD hminor).1
  have hfull : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤ pivotFullImage A C := by
    dsimp only [A, C]
    rw [pivotFullImage_split]
    exact hperiod.trans le_sup_left
  have hi : ((pivotFullImage A C).toAddSubgroup.index : ℝ) ≤
      (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) := by
    exact_mod_cast residueLatticeImage_index_le _ modulus hfull
  have hv' := (mem_spatialWindow_scaled_iff H hH 4 v).mp hv
  have h := vectorSpatialSiteApprox_remesh A (fun _ : X => C) modulus (fun _ => hfull)
    (fun _ => f) (fun _ => hf) H (by positivity)
    (anisotropicSpatialDensityCap_nonneg selection hκ.le) (fun _ => hi) (fun _ => hcap)
    (by norm_num : (0 : ℝ) < 4) hmesh hcoarse v hv'
  simpa only [allocatedResidueSpatialKernel, f, A, C, root, hp, NNReal.coe_mul,
    Real.coe_toNNReal _ (anisotropicSpatialDensityLip_nonneg selection hκ.le)] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset (Fin dim))

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides (allocatedPrincipalSides_pos B U b S)
local notation "frozen" => allocatedFrozenTupleWeights (α := Fin dim) B U b S
local notation "long" => allocatedLongTupleWeights (α := Fin dim) B U b S

variable {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (q : X → ℕ)
variable [NeZero (residueRefinedPeriod modulus q)]
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬(allocatedGridAxis (I := I) U b S.value) a) (allocatedPrincipalSides B U b S))
variable (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U b S.value) a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Module.Basis (Kcov j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (C₀ ρ δ mesh : ℝ) (base : X → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (point : (X → (Unit ⊕ Fin dim) → ℤ) → EuclideanJetLayers U O)
variable (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cg Z : ℝ)

local notation "frozenTuple" => PrincipalAxisTuples (α := Fin dim) grid sides
local notation "label" => (PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a))
  (fun a => layerSamplerDegree I n (Subtype.val a)) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q))
local notation "window" => spatialWindow (α := Fin dim) (trimmedSpatialRootScale τ N q) 4

local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides
local notation "refined" => residueRefinedPeriod modulus q

noncomputable def allocatedResidueWeightedProfileTerm
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) : ℂ :=
  let u := principalAxisRestrict grid y
  let r := principalResidueLabel refined (principalAxisRestrict (fun a => ¬grid a) y)
  let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
  let A := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim)
    (trimmedSpatialRootScale τ N q t) (trimmedSpatialSlopeScale W τ N q t) S.value i
  let reconstruction := allocatedRefinedReferenceReconstruction B U b S x X modulus q reference base cells u r
  ∑ t : cells × window,
    (selectedResidueCellWeight q cells V t.1 : ℂ) *
      (allocatedResidueSpatialKernel B U b S x X hM selection hx modulus
        (trimmedSpatialRootScale τ N q) hW mesh (principalResidueLabel modulus y) t.2.val / (A : ℂ)) *
      test (reconstruction t.1 t.2.val) * profile y (point (reconstruction t.1 t.2.val))

omit [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
  [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
  [NeZero (residueRefinedPeriod modulus q)] in
theorem allocatedWholeProfileReferenceTerm_residue_weighted
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r)
    (profile : fullTuple → EuclideanJetLayers U O → ℂ) (y : fullTuple) :
    allocatedWholeProfileReferenceTerm (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test profile y =
    allocatedResidueWeightedProfileTerm (τ := τ) (ξ := ξ)
      B U b S x X hM selection hx modulus q reference N hW mesh base cells point test profile y := by
  have hker := allocatedRefinedSpatialKernel_whole_residue (τ := τ)
    B U b S x X hM selection hx modulus hW mesh q reference N href y
  simp only [allocatedWholeProfileReferenceTerm, allocatedResidueWeightedProfileTerm,
    allocatedRefinedProfileCoefficient, hker]

noncomputable def allocatedWholeIdealReference (δ : ℝ≥0) : ℂ :=
  let f := physicalActiveProfileIdeal (G := G) (B := B) (G × Option (Fin dim)) (layerSamplerDegree I n)
    grid (fun a => rows a.val.1) (fun a => R a.1) (fun a => hR a.1) δ
  (whole).complexMean (allocatedResidueWeightedProfileTerm (τ := τ) (ξ := ξ)
    B U b S x X hM selection hx modulus q reference N hW mesh base cells point test
    (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y modulus f z : ℂ))) /
      (Z : ℂ)

omit [∀ j, DecidableEq (O j)] in
theorem allocatedRefinedIdealReference_residue_weighted (δ : ℝ≥0)
    (hperiod : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hRefined : 0 < refined)
    (hsize : ∀ a, (Fintype.card (Fin dim) + 1) * refined ≤
      principalAxisLength (fun a => ¬grid a) sides a)
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r)
    (hresidue : ∀ u r v,
      (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 →
      ∀ j, integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j) :
    allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
      N hW mesh base cells point test Z δ =
    allocatedWholeIdealReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus q reference hb o bW d
      N hW mesh base cells point test Z δ := by
  let f := physicalActiveProfileIdeal (G := G) (B := B) (G × Option (Fin dim)) (layerSamplerDegree I n)
    grid (fun a => rows a.val.1) (fun a => R a.1) (fun a => hR a.1) δ
  have h := allocatedRefinedFamilyReference_whole (τ := τ) (ξ := ξ)
    B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
    N hW mesh base cells point test Z hperiod hRefined hsize href hresidue
    (fun r => allocatedLongProfileDensity B U b S x rows modulus r f) (fun _ => 1)
  have hfirst : allocatedRefinedIdealReference (τ := τ) (ξ := ξ)
      B U b hR hσ S x rows X hM selection hx modulus q reference residue hb o bW d
      N hW mesh base cells point test Z δ =
      (whole).complexMean (allocatedWholeProfileReferenceTerm (τ := τ) (ξ := ξ)
        B U b S x X hM selection hx modulus q reference N hW mesh base cells point test
        (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y modulus f z : ℂ))) /
          (Z : ℂ) := by
    rw [allocatedRefinedIdealReference_as_complex]
    simpa only [mul_one, allocatedRefinedIdealProfile, allocatedWholeResidueProfile,
      allocatedWholeMaskedCoveredProfile] using h
  rw [hfirst]
  unfold allocatedWholeIdealReference
  apply congrArg (fun z : ℂ => z / (Z : ℂ))
  apply congrArg (whole).complexMean
  funext y
  exact allocatedWholeProfileReferenceTerm_residue_weighted (τ := τ) (ξ := ξ)
    B U b S x X hM selection hx modulus q reference N hW mesh base cells point test href _ y

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

theorem exists_allocatedWholeResidueReference (modulus : ℕ) (hmodulus : 0 < modulus)
    (hsize : ∀ a, (Fintype.card (Fin dim) + 1) * modulus ≤ sides a) :
    ∃ reference : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus) → fullTuple,
      ∀ r, principalResidueLabel modulus (reference r) = r ∧
        (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) sides
          (allocatedPrincipalSides_pos B U b S)).weight (reference r) ≠ 0 := by
  have h := fun r => principalResidue_positive_witness B (layerSamplerDegree I n) sides
    (allocatedPrincipalSides_pos B U b S) modulus hmodulus hsize r
  exact ⟨fun r => (h r).choose, fun r => (h r).choose_spec⟩

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

noncomputable def allocatedReferenceTupleOfWhole (y : fullTuple) : fullTuple :=
  principalAxisJoin grid (principalAxisRestrict grid y)
    (reference (principalAxisRestrict grid y)
      (principalResidueLabel refined (principalAxisRestrict (fun a => ¬grid a) y)))

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedReferenceTupleOfWhole_label
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r) (y : fullTuple) :
    principalResidueLabel refined (allocatedReferenceTupleOfWhole B U b S X modulus q reference y) =
      principalResidueLabel refined y := by
  unfold allocatedReferenceTupleOfWhole
  rw [principalResidueLabel_join, href, ← principalResidueLabel_join, principalAxisJoin_restrict]

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)

noncomputable def allocatedWholeResidueReconstruction (base : X → ℤ)
    (r : labels) (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q) :=
  physicalResidueReconstruction
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (wholeReference r))
    (allocatedPhysicalCubeDirections B U b S x (wholeReference r)) base
    (boundedColumnResidueRepresentative q a) q

noncomputable def allocatedResidueReferenceShift (y : fullTuple)
    (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q) :=
  let old := allocatedReferenceTupleOfWhole B U b S X modulus q reference y
  let chosen := wholeReference (principalResidueLabel refined y)
  physicalResidueOffsetShift
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x old)
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x chosen)
    (allocatedPhysicalCubeDirections B U b S x old)
    (allocatedPhysicalCubeDirections B U b S x chosen)
    (boundedColumnResidueRepresentative q a) q

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedResidueReferenceShift_spec
    (hq : ∀ t, 0 < q t)
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r)
    (hwhole : ∀ r, principalResidueLabel refined (wholeReference r) = r)
    (base : X → ℤ) (y : fullTuple)
    (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q) :
    let shift := allocatedResidueReferenceShift B U b S X modulus q reference wholeReference x y a
    (∀ t, shift t ∈ integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ)) ∧
    (∀ v, physicalResidueReconstruction
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x
        (allocatedReferenceTupleOfWhole B U b S X modulus q reference y))
      (allocatedPhysicalCubeDirections B U b S x
        (allocatedReferenceTupleOfWhole B U b S X modulus q reference y)) base
      (boundedColumnResidueRepresentative q a) q v =
        allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
          (principalResidueLabel refined y) a (v + shift)) ∧
    (∀ t i, |(shift t i : ℝ)| ≤ Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) := by
  have hlabel : principalResidueLabel refined
      (allocatedReferenceTupleOfWhole B U b S X modulus q reference y) =
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) := by
    rw [allocatedReferenceTupleOfWhole_label B U b S X modulus q reference href, hwhole]
  have hrep (k) (t) : |(boundedColumnResidueRepresentative q a (k,t) : ℝ)| ≤ q t := by
    have h := boundedColumnResidueRepresentative_bounds q hq a (k,t)
    rw [abs_of_nonneg (by exact_mod_cast h.1 :
      (0 : ℝ) ≤ boundedColumnResidueRepresentative q a (k,t))]
    exact_mod_cast h.2.le
  exact allocatedPhysicalResidue_whole_offset_shift B U b S (fun _ => 0) x
    (allocatedReferenceTupleOfWhole B U b S X modulus q reference y)
    (wholeReference (principalResidueLabel refined y)) base
    (boundedColumnResidueRepresentative q a) q hq modulus refined
    (stride_mul_dvd_residueRefinedPeriod modulus q) hlabel hrep

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedResidueReferenceShift_normalized
    (hq : ∀ t, 0 < q t)
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r)
    (hwhole : ∀ r, principalResidueLabel refined (wholeReference r) = r)
    (H : X → ℝ) (hH : ∀ t, 0 < H t) {ε : ℝ} (hε : 0 ≤ ε)
    (hsize : ∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ ε * H t)
    (y : fullTuple) (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q) :
    ∀ t, ‖fun i => ((allocatedResidueReferenceShift B U b S X modulus q reference wholeReference x y a t i : ℤ) : ℝ) /
      H t‖ ≤ ε := by
  have hbound := (allocatedResidueReferenceShift_spec B U b S X modulus q reference wholeReference x
    hq href hwhole (fun _ => 0) y a).2.2
  intro t
  apply (pi_norm_le_iff_of_nonneg hε).2
  intro i
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hH t)]
  exact (div_le_iff₀ (hH t)).mpr ((hbound t i).trans (hsize t))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "sides" => allocatedPrincipalSides B U b S
local notation "fullTuple" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) sides

variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
    (allocatedPrincipalSides B U b S) →
  (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
    (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
    (allocatedPrincipalSides B U b S))
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))

local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedResidueReferenceShift_spec_at
    (hq : ∀ t, 0 < q t)
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r)
    (base : X → ℤ) (y : fullTuple)
    (hwhole : principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q) :
    let shift := allocatedResidueReferenceShift B U b S X modulus q reference wholeReference x y a
    (∀ t, shift t ∈ integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ)) ∧
    (∀ v, physicalResidueReconstruction
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x
        (allocatedReferenceTupleOfWhole B U b S X modulus q reference y))
      (allocatedPhysicalCubeDirections B U b S x
        (allocatedReferenceTupleOfWhole B U b S X modulus q reference y)) base
      (boundedColumnResidueRepresentative q a) q v =
        allocatedWholeResidueReconstruction B U b S X modulus q wholeReference x base
          (principalResidueLabel refined y) a (v + shift)) ∧
    (∀ t i, |(shift t i : ℝ)| ≤ Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) := by
  have hlabel : principalResidueLabel refined
      (allocatedReferenceTupleOfWhole B U b S X modulus q reference y) =
      principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) := by
    rw [allocatedReferenceTupleOfWhole_label B U b S X modulus q reference href, hwhole]
  have hrep (k) (t) : |(boundedColumnResidueRepresentative q a (k,t) : ℝ)| ≤ q t := by
    have h := boundedColumnResidueRepresentative_bounds q hq a (k,t)
    rw [abs_of_nonneg (by exact_mod_cast h.1 :
      (0 : ℝ) ≤ boundedColumnResidueRepresentative q a (k,t))]
    exact_mod_cast h.2.le
  exact allocatedPhysicalResidue_whole_offset_shift B U b S (fun _ => 0) x
    (allocatedReferenceTupleOfWhole B U b S X modulus q reference y)
    (wholeReference (principalResidueLabel refined y)) base
    (boundedColumnResidueRepresentative q a) q hq modulus refined
    (stride_mul_dvd_residueRefinedPeriod modulus q) hlabel hrep

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedResidueReferenceShift_normalized_at
    (hq : ∀ t, 0 < q t)
    (href : ∀ u r, principalResidueLabel refined (reference u r) = r)
    (H : X → ℝ) (hH : ∀ t, 0 < H t) {ε : ℝ} (hε : 0 ≤ ε)
    (hsize : ∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ ε * H t)
    (y : fullTuple) (hwhole : principalResidueLabel refined (wholeReference (principalResidueLabel refined y)) = principalResidueLabel refined y)
    (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q) :
    ∀ t, ‖fun i => ((allocatedResidueReferenceShift B U b S X modulus q reference wholeReference x y a t i : ℤ) : ℝ) /
      H t‖ ≤ ε := by
  have hbound := (allocatedResidueReferenceShift_spec_at B U b S X modulus q reference wholeReference x
    hq href (fun _ => 0) y hwhole a).2.2
  intro t
  apply (pi_norm_le_iff_of_nonneg hε).2
  intro i
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hH t)]
  exact (div_le_iff₀ (hH t)).mpr ((hbound t i).trans (hsize t))

end Erdos3.VectorPolynomial

end

end OAI
