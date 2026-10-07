/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.PrincipalSpatialSiteComparison
import OAI.Combinatorics.Progressions.Geometry.SupportedMeanBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residueSpatialSite_norm_le {D I J N : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [Fintype N]
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : D → ((Unit ⊕ I) → ℝ) → ℝ) (H : D → ℝ)
    {b r C : ℝ} (hb : 0 < b) (hr : 0 < r) (_hC : 0 ≤ C) (hf : ∀ d y, |f d y| ≤ C)
    (residue : D → Matrix (Unit ⊕ I) N (ZMod m)) (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ)/H d| ≤ b) :
    ‖∏ d, spatialSiteApprox A (Matrix.fromCols B (liftResidueMatrix (residue d))) m (f d) (H d) b r (v d)‖ ≤
      ((m : ℝ)^Fintype.card (Unit ⊕ I)*C)^Fintype.card D := by
  have hfull (d : D) : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage A (Matrix.fromCols B (liftResidueMatrix (residue d))) := by
    rw [pivotFullImage_split]
    exact hp.trans le_sup_left
  have hi (d : D) :
      ((pivotFullImage A (Matrix.fromCols B (liftResidueMatrix (residue d)))).toAddSubgroup.index : ℝ) ≤
        (m : ℝ)^Fintype.card (Unit ⊕ I) := by
    exact_mod_cast residueLatticeImage_index_le _ m (hfull d)
  calc
    _ ≤ ∏ d, ‖spatialSiteApprox A (Matrix.fromCols B (liftResidueMatrix (residue d))) m (f d) (H d) b r (v d)‖ :=
      (norm_prod _ _).le
    _ ≤ ∏ _d : D, (m : ℝ)^Fintype.card (Unit ⊕ I)*C :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun d _ =>
        spatialSiteApprox_norm_le A _ m (f d) (H d) hb hr (hi d) (hf d) (v d) (hv d))
    _ = _ := by simp

theorem residueSpatialSite_mean_norm_le {R V D I J N : Type*}
    [Fintype R] [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [Fintype N]
    (p : FiniteProbabilityWeights R) (t : Finset V) (out : V → D → (Unit ⊕ I) → ℤ)
    (A : Matrix (Unit ⊕ I) (Unit ⊕ I) ℤ) (B : Matrix (Unit ⊕ I) J ℤ)
    (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤ pivotFullImage A B)
    (f : D → ((Unit ⊕ I) → ℝ) → ℝ) (H : D → ℝ)
    {b r C : ℝ} (hb : 0 < b) (hr : 0 < r) (hC : 0 ≤ C) (hf : ∀ d y, |f d y| ≤ C)
    (residue : R → D → Matrix (Unit ⊕ I) N (ZMod m))
    (hv : ∀ v ∈ t, ∀ d i, |((spatialStar (out v d) i : ℤ) : ℝ)/H d| ≤ b) :
    p.mean (fun a => 𝔼 v ∈ t,
      ‖∏ d, spatialSiteApprox A (Matrix.fromCols B (liftResidueMatrix (residue a d)))
        m (f d) (H d) b r (out v d)‖) ≤ ((m : ℝ)^Fintype.card (Unit ⊕ I)*C)^Fintype.card D := by
  apply finiteMean_le_of_support
  intro a _
  apply finite_expect_le_of_nonneg_bound t _ (by positivity)
  intro v hvt
  exact residueSpatialSite_norm_le A B m hp f H hb hr hC hf (residue a) (out v) (hv v hvt)

theorem smoothSpatialSite_mean_norm_le {R V D I J N : Type*}
    [Fintype R] [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype N] {L M : ℕ} (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hM : 0 < M) (hL : 0 < L) (hx : GoodScalarKernelTuple s (1/(M : ℝ)) M x)
    (hroot : ∀ j, |root j| ≤ (L : ℤ)) (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s))
    (H : D → ℝ) (hH : ∀ d, 0 < H d) {b r : ℝ} (hb : 0 < b) (hr : 0 < r)
    (p : FiniteProbabilityWeights R) (t : Finset V) (out : V → D → (Unit ⊕ I) → ℤ)
    (residue : R → D → Matrix (Unit ⊕ I) N (ZMod m))
    (hv : ∀ v ∈ t, ∀ d i, |((spatialStar (out v d) i : ℤ) : ℝ)/H d| ≤ b) :
    let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let B := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hM)) hx
    let f := fun d => smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hA
      (H d) L (hH d) (by exact_mod_cast hL)
    p.mean (fun a => 𝔼 v ∈ t,
      ‖∏ d, spatialSiteApprox A (Matrix.fromCols B (liftResidueMatrix (residue a d)))
        m (f d) (H d) b r (out v d)‖) ≤
      ((m : ℝ)^Fintype.card (Unit ⊕ I)*smoothSpatialDensityCap s M)^Fintype.card D := by
  dsimp only
  exact residueSpatialSite_mean_norm_le p t out _ _ m hp _ H hb hr
    (smoothSpatialDensityCap_nonneg s M)
    (fun d => (smoothSpatialKernelDensity_bounds s x root hM hL (hH d) hx hroot).1) residue hv

end Erdos3

end

end OAI
