/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.PhysicalCubeWindowReindex

namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators Classical

variable {K X α : Type*} [Fintype K] [Fintype X] [Fintype α]
variable (root : K → ℤ) (D : Matrix α K ℤ) (base : X → ℤ)
variable (residue : Option K × X → ℤ) (q : X → ℕ) (H : X → ℝ) (radius : ℝ)

noncomputable def physicalResidueWindowSiteMask (s : Finset α) (u : X → ℤ) : ℂ :=
  starVertexSiteFactor (fun i v => if ∀ x,
    |(((v x - physicalCubeVertexValue (physicalCubeRootDifferences root D base residue)
      (spatialStarVertex i) x) / (q x : ℤ) : ℤ) : ℝ)| ≤ H x * radius then 1 else 0) s u

theorem physicalResidueWindowSiteMask_bound (s : Finset α) (u : X → ℤ) :
    ‖physicalResidueWindowSiteMask root D base residue q H radius s u‖ ≤ 1 := by
  apply starVertexSiteFactor_bound
  intro i v
  split_ifs <;> norm_num

theorem physicalResidueWindowSiteMask_prod_reconstruction
    (hq : ∀ x, 0 < q x) (v : X → (Unit ⊕ α) → ℤ) :
    (∏ s, physicalResidueWindowSiteMask root D base residue q H radius s
      (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s)) =
      if v ∈ spatialWindow H radius then 1 else 0 := by
  simp only [physicalResidueWindowSiteMask, starVertexSiteFactor_prod]
  have he (i : Unit ⊕ α) (x : X) :
      ((physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v)
        (spatialStarVertex i) x - physicalCubeVertexValue (physicalCubeRootDifferences root D base residue)
          (spatialStarVertex i) x) / (q x : ℤ)) = spatialStar (v x) i := by
    rw [physicalCubeVertexValue_residueReconstruction, add_sub_cancel_left,
      Int.mul_ediv_cancel_left _ (by exact_mod_cast (hq x).ne'), physicalCubeVertexValue_star]
  simp only [he]
  by_cases hv : v ∈ spatialWindow H radius
  · rw [ite_eq_left hv]
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_left (fun x => (mem_spatialWindow_iff H radius v).mp hv x i)
  · rw [ite_eq_right hv]
    have hn : ¬ ∀ i x, |((spatialStar (v x) i : ℤ) : ℝ)| ≤ H x * radius := by
      intro h
      exact hv ((mem_spatialWindow_iff H radius v).mpr (fun x i => h i x))
    push Not at hn
    obtain ⟨i, x, hx⟩ := hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right (fun h => (not_le_of_gt hx) (h x))

variable [DecidableEq X]

theorem physicalResidueWindow_masked_sum_eq_box_sum
    {dim : ℕ} (D : Matrix (Fin dim) K ℤ) (N : X → ℕ) (hq : ∀ x, 0 < q x)
    (f : Finset (Fin dim) → (X → ℤ) → ℂ)
    (hbox : ∀ u, (∏ s, f s (physicalCubeVertexValue u s)) ≠ 0 →
      ∀ s, physicalCubeVertexValue u s ∈ integerBox N)
    (hresidue : ∀ u, (∏ s, f s (physicalCubeVertexValue u s)) ≠ 0 →
      u ∈ Set.range (physicalResidueReconstruction root D base residue q)) :
    (∑ v ∈ spatialWindow H radius,
      ∏ s, f s (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s)) =
      ∑ u ∈ physicalIntegerBoxCubes N dim,
        ∏ s, physicalResidueWindowSiteMask root D base residue q H radius s (physicalCubeVertexValue u s) *
          f s (physicalCubeVertexValue u s) := by
  let mask := physicalResidueWindowSiteMask root D base residue q H radius
  let φ := fun u => ∏ s, mask s (physicalCubeVertexValue u s) * f s (physicalCubeVertexValue u s)
  have hnonzero (u) (hu : φ u ≠ 0) : (∏ s, f s (physicalCubeVertexValue u s)) ≠ 0 := by
    dsimp only [φ] at hu
    rw [Finset.prod_mul_distrib] at hu
    exact (mul_ne_zero_iff.mp hu).2
  have hpull (v) : φ (physicalResidueReconstruction root D base residue q v) =
      (if v ∈ spatialWindow H radius then 1 else 0) *
        ∏ s, f s (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s) := by
    dsimp only [φ, mask]
    rw [Finset.prod_mul_distrib, physicalResidueWindowSiteMask_prod_reconstruction root D base residue q H radius hq]
  calc
    _ = ∑ v ∈ spatialWindow H radius, φ (physicalResidueReconstruction root D base residue q v) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [hpull, ite_eq_left hv, one_mul]
    _ = _ := physicalResidueWindow_sum_eq_box_sum root D base residue q N hq (spatialWindow H radius) φ
      (fun v _ hv => hbox _ (hnonzero _ hv))
      (fun v hv => by rw [hpull, ite_eq_right hv, zero_mul])
      (fun u hu => hresidue u (hnonzero u hu))

theorem physicalResidueWindow_norm_le_cube_mean
    {dim : ℕ} (D : Matrix (Fin dim) K ℤ) (N : X → ℕ) (hq : ∀ x, 0 < q x)
    (f : Finset (Fin dim) → (X → ℤ) → ℂ)
    (hbox : ∀ u, (∏ s, f s (physicalCubeVertexValue u s)) ≠ 0 →
      ∀ s, physicalCubeVertexValue u s ∈ integerBox N)
    (hresidue : ∀ u, (∏ s, f s (physicalCubeVertexValue u s)) ≠ 0 →
      u ∈ Set.range (physicalResidueReconstruction root D base residue q))
    {volume C : ℝ} (hvolume : 0 < volume)
    (hratio : (integerBoxCubeCount N dim : ℝ) / volume ≤ C) :
    ‖(∑ v ∈ spatialWindow H radius,
      ∏ s, f s (physicalCubeVertexValue (physicalResidueReconstruction root D base residue q v) s)) /
        (volume : ℂ)‖ ≤
      C * ‖𝔼 cube : SupportedCube dim (integerBox N : Set (X → ℤ)),
        let u := (physicalCubeParametersEquiv X dim).symm cube.val
        ∏ s, physicalResidueWindowSiteMask root D base residue q H radius s (physicalCubeVertexValue u s) *
          f s (physicalCubeVertexValue u s)‖ := by
  rw [physicalResidueWindow_masked_sum_eq_box_sum root base residue q H radius D N hq f hbox hresidue,
    physicalIntegerBoxCubes_sum_eq_count_mul_mean]
  rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hvolume.le]
  rw [mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

end Erdos3.BooleanCubeKernel

end

end OAI
