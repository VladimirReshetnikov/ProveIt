/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.SlicedPrincipalInverse

namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff

variable {B F : Type*} [Fintype B] [Fintype F]

noncomputable def principalSlicePolynomial (c : B → ℝ) (lower width : B × F → ℝ) :
    MvPolynomial (B × F) ℝ :=
  ∑ b, MvPolynomial.C (c b) * ∏ i,
    (MvPolynomial.C (lower (b, i)) + MvPolynomial.C (width (b, i)) * MvPolynomial.X (b, i))

theorem principalSlicePolynomial_eval [DecidableEq B] [DecidableEq F]
    (c : B → ℝ) (lower width : B × F → ℝ) (x : B × F → ℝ) :
    MvPolynomial.eval x (principalSlicePolynomial c lower width) = principalSliceValue c lower width x := by
  simp [principalSlicePolynomial, principalSliceValue]

theorem principalSlicePolynomial_degree (c : B → ℝ) (lower width : B × F → ℝ) :
    (principalSlicePolynomial c lower width).totalDegree ≤ Fintype.card F := by
  classical
  apply MvPolynomial.totalDegree_finsetSum_le
  intro b _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : F, 1 := Finset.sum_le_sum (fun i _ => by
      apply (MvPolynomial.totalDegree_add _ _).trans
      apply max_le (by simp)
      exact (MvPolynomial.totalDegree_mul _ _).trans (by simp))
    _ = _ := by simp

theorem principalSlicePolynomial_mass (c : B → ℝ) (lower width : B × F → ℝ)
    (hwidth : ∀ p, |lower p| + |width p| ≤ 1) :
    realPolynomialMass (principalSlicePolynomial c lower width) ≤ ∑ b, |c b| := by
  classical
  apply (realPolynomialMass_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  apply (realPolynomialMass_C_mul_le _ _).trans
  apply mul_le_of_le_one_right (abs_nonneg _)
  apply (realPolynomialMass_prod_le _ _).trans
  apply Finset.prod_le_one₀ (fun _ _ => realPolynomialMass_nonneg _)
  intro i _
  apply (realPolynomialMass_add_le _ _).trans
  calc
    _ ≤ |lower (b, i)| + |width (b, i)| := by
      rw [realPolynomialMass_C]
      apply add_le_add le_rfl
      simpa only [realPolynomialMass_X, mul_one] using
        realPolynomialMass_C_mul_le (width (b, i)) (MvPolynomial.X (b, i))
    _ ≤ 1 := hwidth (b, i)

section Joint

variable {D : Type*} [Fintype D] {B F : D → Type*}
variable [∀ d, Fintype (B d)] [∀ d, Fintype (F d)]
variable [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (F d)]

noncomputable def jointSlicedPolynomial (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) (o : Σ _d : D, Unit) :
    MvPolynomial (Σ d, B d × F d) ℝ :=
  MvPolynomial.rename (Sigma.mk o.1) (principalSlicePolynomial (c o.1) (lower o.1) (width o.1))

omit [Fintype D] in
theorem jointSlicedPolynomial_map (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) :
    polynomialVectorMap (jointSlicedPolynomial c lower width) = jointSlicedPrincipal c lower width := by
  funext x o
  change MvPolynomial.eval x (MvPolynomial.rename _ _) = _
  rw [MvPolynomial.eval_rename, principalSlicePolynomial_eval]
  rfl

theorem jointSlicedPrincipal_c2_bounds (c : ∀ d, B d → ℝ)
    (lower width : ∀ d, B d × F d → ℝ) {m : ℕ}
    (hdegree : ∀ d, Fintype.card (F d) ≤ m)
    (hwidth : ∀ d p, |lower d p| + |width d p| ≤ 1)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ d, (∑ b, |c d b|) ≤ C)
    (x : (Σ d, B d × F d) → ℝ) (hx : ∀ p, |x p| ≤ 1) :
    let N := Fintype.card (Σ d, B d × F d)
    ‖jointSlicedPrincipal c lower width x‖ ≤ C ∧
      ‖fderiv ℝ (jointSlicedPrincipal c lower width) x‖ ≤ N * ((m : ℝ) * C) ∧
      ‖fderiv ℝ (fderiv ℝ (jointSlicedPrincipal c lower width)) x‖ ≤
        N * (N * ((m : ℝ) * ((m : ℝ) * C))) := by
  classical
  have hd (o : Σ _d : D, Unit) (p : Σ d, B d × F d) :
      (jointSlicedPolynomial c lower width o).degreeOf p ≤ m :=
    (MvPolynomial.degreeOf_le_totalDegree _ _).trans
      ((MvPolynomial.totalDegree_rename_le _ _).trans
        ((principalSlicePolynomial_degree _ _ _).trans (hdegree o.1)))
  have hm (o : Σ _d : D, Unit) : realPolynomialMass (jointSlicedPolynomial c lower width o) ≤ C :=
    (realPolynomialMass_rename_le _ _).trans
      ((principalSlicePolynomial_mass _ _ _ (hwidth o.1)).trans (hc o.1))
  have h := polynomialVectorMap_mass_c2_bounds (jointSlicedPolynomial c lower width) hd hC hm x hx
  rwa [jointSlicedPolynomial_map] at h

end Joint

end Erdos3

end

end OAI
