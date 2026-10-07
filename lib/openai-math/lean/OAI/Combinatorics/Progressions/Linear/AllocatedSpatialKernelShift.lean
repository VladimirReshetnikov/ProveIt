import OAI.Combinatorics.Progressions.Lattices.AllocatedLocalResidueReconstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (X : Type*) [Fintype X] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (modulus : ℕ) [NeZero modulus] (H : X → ℝ) {W : ℝ} (hW : 0 ≤ W) (mesh : ℝ)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedResidueSpatialKernel_shift
    (Q : ℝ≥0) (hQ : 1 ≤ Q) (hratio : (1 + W) / (S.value : ℝ) ≤ Q)
    (hroot : ∀ g, |((x g none : ℤ) : ℝ)| ≤ 1 + W)
    (hperiod : integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection))
    (hH : ∀ t, 0 < H t) (hmesh : 0 < mesh) {ε : ℝ} (hε : 0 ≤ ε)
    (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod modulus)
    (v shift : X → (Unit ⊕ Fin dim) → ℤ)
    (hshift : ∀ t, shift t ∈ integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ))
    (hsize : ∀ t, ‖fun i => (shift t i : ℝ) / H t‖ ≤ ε)
    (hv : v ∈ spatialWindow H 4) (hvs : v + shift ∈ spatialWindow H 4) :
    ‖allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r (v + shift) -
      allocatedResidueSpatialKernel B U b S x X hM selection hx modulus H hW mesh r v‖ ≤
      Fintype.card X *
        ((modulus : ℝ)^Fintype.card (Unit ⊕ Fin dim) *
          (anisotropicSpatialDensityLip selection (1 / (M : ℝ)) * Q) * (8 * mesh + ε)) *
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
  have h := vectorSpatialSiteApprox_shift A (fun _ : X => C) modulus (fun _ => hfull)
    (fun _ => f) (fun _ => hf) H (by positivity)
    (anisotropicSpatialDensityCap_nonneg selection hκ.le) hε (fun _ => hi) (fun _ => hcap)
    (by norm_num : (0 : ℝ) < 4) hmesh v shift (fun t => hfull (hshift t)) hsize
    ((mem_spatialWindow_scaled_iff H hH 4 v).mp hv)
    ((mem_spatialWindow_scaled_iff H hH 4 (v + shift)).mp hvs)
  simpa only [allocatedResidueSpatialKernel, f, A, C, root, hp, Pi.add_apply, NNReal.coe_mul,
    Real.coe_toNNReal _ (anisotropicSpatialDensityLip_nonneg selection hκ.le)] using h

end Erdos3.VectorPolynomial

end

end OAI
