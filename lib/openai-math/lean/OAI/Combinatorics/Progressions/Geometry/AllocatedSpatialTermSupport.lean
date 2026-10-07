import OAI.Combinatorics.Progressions.Linear.AllocatedSpatialKernelShift

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)

omit [DecidableEq G] in
theorem allocatedKernel_coefficient_sum {W : ℝ}
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (c : Option (Fin dim)) : (∑ g, |((x g c : ℤ) : ℝ)|) ≤ W := by
  have hcard : Fintype.card G ≤ Fintype.card (LayerSamplerVariables G I n B) :=
    Fintype.card_le_of_injective (Sum.inl : G → LayerSamplerVariables G I n B) Sum.inl_injective
  have hwb : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * (S.value : ℝ) ≤ W := by
    simpa only [allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero, zero_add] using hbudget
  have hsum : (∑ g, |((x g c : ℤ) : ℝ)|) ≤ (Fintype.card G : ℝ) * S.value := by
    calc
      _ ≤ ∑ _g : G, (S.value : ℝ) := by
        apply Finset.sum_le_sum
        intro g _
        have hg := Finset.mem_Ico.mp (x g c).property
        exact_mod_cast abs_le.mpr ⟨hg.1, hg.2.le⟩
      _ = _ := by simp
  exact hsum.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (Nat.cast_nonneg S.value)).trans hwb)

variable (X : Type*) [Fintype X] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ) {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

theorem allocatedResidueSpatialKernel_zero_outside
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hH : ∀ t, 0 < H t) (hmesh : 0 < mesh)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (hv : v ∉ spatialWindow H (3 + 2 * mesh)) :
    allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r v = 0 := by
  have hcoords : ¬ ∀ t i, |((spatialStar (v t) i : ℤ) : ℝ) / H t| ≤ 3 + 2 * mesh :=
    fun h => hv ((mem_spatialWindow_scaled_iff H hH (3 + 2 * mesh) v).2 h)
  push Not at hcoords
  obtain ⟨t, i, hi⟩ := hcoords
  let root := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x root
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  have hroot : (∑ g, |(root g : ℝ)|) ≤ W := by
    simpa only [root, zero_add] using allocatedKernel_coefficient_sum B U b S x hbudget none
  have hD : ∀ i, (∑ g, |(scalarCubeDifferenceMatrix x i g : ℝ)|) ≤ 1 + W := by
    intro i
    have h := allocatedKernel_coefficient_sum B U b S x hbudget (some i)
    change (∑ g, |((x g (some i) : ℤ) : ℝ)|) ≤ 1 + W
    linarith
  unfold allocatedResidueSpatialKernel
  apply Finset.prod_eq_zero (Finset.mem_univ t)
  apply spatialSiteApprox_zero_outside _ _ modulus _ (H t) 4 mesh 3 hmesh
  · exact canonicalSpatialSiteDensity_zero_outside selection root (scalarCubeDifferenceMatrix x)
      hp hW (Nat.cast_pos.mpr S.positive) hroot hD
  · exact ⟨i, hi⟩

theorem allocatedResidueSpatialWindowWeight_eq_kernel
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hH : ∀ t, 0 < H t) (hmesh : 0 < mesh) (hmargin : 3 + 2 * mesh ≤ 4)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
    (v : X → (Unit ⊕ Fin dim) → ℤ) :
    allocatedResidueSpatialWindowWeight B U b S x X hM selection hx modulus H hW mesh r v =
      allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r v := by
  unfold allocatedResidueSpatialWindowWeight
  split_ifs with hv
  · rfl
  · symm
    apply allocatedResidueSpatialKernel_zero_outside B U b S x X hM selection hx modulus H hW mesh
      hbudget hH hmesh r v
    exact fun h => hv (spatialWindow_radius_mono H (fun t => (hH t).le) hmargin h)

theorem allocatedResidueSpatialKernel_shift_global
    (Q : ℝ≥0) (hQ : 1 ≤ Q) (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hH : ∀ t, 0 < H t) (hmesh : 0 < mesh) {ε : ℝ} (hε : 0 ≤ ε)
    (hmargin : (3 + 2 * mesh) + 2 * ε ≤ 4)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
    (shift : X → (Unit ⊕ Fin dim) → ℤ)
    (hshift : ∀ t, shift t ∈ integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ))
    (hsize : ∀ t, ‖fun i => (shift t i : ℝ) / H t‖ ≤ ε) :
    ∀ v, ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r (v + shift) -
      allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r v‖ ≤
      Fintype.card X *
        ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (8 * mesh + ε)) *
        (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X := by
  have hroot (g) : |((x g none : ℤ) : ℝ)| ≤ 1 + W := by
    have h := (Finset.single_le_sum (fun j _ => abs_nonneg (((x j none : ℤ) : ℝ)))
      (Finset.mem_univ g)).trans (allocatedKernel_coefficient_sum B U b S x hbudget none)
    linarith
  have hs : shift ∈ spatialWindow H (2 * ε) := by
    apply spatialWindow_of_coordinate_bound H (fun t => (hH t).le) hε shift
    intro t i
    have h := (norm_le_pi_norm (fun i => (shift t i : ℝ) / H t) i).trans (hsize t)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hH t)] at h
    have hd := (div_le_iff₀ (hH t)).mp h
    simpa only [mul_comm] using hd
  have hκ : 0 ≤ 1 / (M : ℝ) := one_div_nonneg.mpr (Nat.cast_nonneg M)
  have hLip := anisotropicSpatialDensityLip_nonneg selection hκ
  have hCap := anisotropicSpatialDensityCap_nonneg selection hκ
  have hE : 0 ≤ Fintype.card X *
      ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
        (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (8 * mesh + ε)) *
      (1 + (modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
        anisotropicSpatialDensityCap selection (1 / (M : ℝ)))^Fintype.card X := by positivity
  apply spatialWeight_shift_global H (fun t => (hH t).le)
    (allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r)
    (by positivity : 0 ≤ 2 * ε) hE hmargin
    (allocatedResidueSpatialKernel_zero_outside B U b S x X hM selection hx modulus H hW mesh hbudget hH hmesh r)
    shift hs
  intro v hv hvs
  exact allocatedResidueSpatialKernel_shift B U b S x X hM selection hx modulus H hW mesh
    Q hQ hratio hroot hperiod hH hmesh hε r v shift hshift hsize hv hvs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)

variable (X : Type*) [Fintype X] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ) {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

omit [NeZero modulus] in
theorem allocatedSpatialExpansionCoefficient_term_zero_outside
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hH : ∀ z, 0 < H z) (hmesh : 0 < mesh) (hmargin : 3 + 2 * mesh ≤ 4)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
    (t : X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
    (hc : allocatedSpatialExpansionCoefficient B U b S x X hM selection hx modulus hW mesh r t ≠ 0)
    (v : X → (Unit ⊕ Fin dim) → ℤ) (hv : v ∉ spatialWindow H 4) :
    (∏ i, vectorResidueSiteWeight 4 mesh H (fun z => (t z).1 i) (fun z => (t z).2 i)
      (fun z => spatialStar (v z) i)) = 0 := by
  have hcoords : ¬ ∀ z i, |((spatialStar (v z) i : ℤ) : ℝ) / H z| ≤ 4 :=
    fun h => hv ((mem_spatialWindow_scaled_iff H hH 4 v).2 h)
  push Not at hcoords
  obtain ⟨z, i, hi⟩ := hcoords
  let root := fun g => (0 : ℤ) + (x g none : ℤ)
  let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x root
    (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
  have hroot : (∑ g, |(root g : ℝ)|) ≤ W := by
    simpa only [root, zero_add] using allocatedKernel_coefficient_sum B U b S x hbudget none
  have hD : ∀ i, (∑ g, |(scalarCubeDifferenceMatrix x i g : ℝ)|) ≤ 1 + W := by
    intro i
    have h := allocatedKernel_coefficient_sum B U b S x hbudget (some i)
    change (∑ g, |((x g (some i) : ℤ) : ℝ)|) ≤ 1 + W
    linarith only [h]
  let f := canonicalSpatialSiteDensity selection root (scalarCubeDifferenceMatrix x) hp W S.value
    hW (Nat.cast_pos.mpr S.positive)
  let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection
  let Bextra := Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)
    (liftResidueMatrix (principalSpatialResidueColumns modulus (fun _ => (0 : ℤ)) id r))
  have hcz : spatialSiteCoefficient A Bextra modulus f 4 mesh (t z) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hc) z (Finset.mem_univ z)
  have hz := spatialSiteTerm_zero_outside A Bextra modulus f (H z) 4 mesh 3 hmesh
    (canonicalSpatialSiteDensity_zero_outside selection root (scalarCubeDifferenceMatrix x)
      hp hW (Nat.cast_pos.mpr S.positive) hroot hD) (t z) (v z) ⟨i, hmargin.trans_lt hi⟩
  simp only [vectorResidueSiteWeight]
  rw [Finset.prod_comm]
  exact Finset.prod_eq_zero (Finset.mem_univ z) ((mul_eq_zero.mp hz).resolve_left hcz)

end Erdos3.VectorPolynomial

end

end OAI
