import OAI.Combinatorics.Progressions.Geometry.MarkedDirectionCoordinates

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem direction_lattice_scale_bound (d t B H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hB : (B : ℝ) ≤ Real.exp p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((B * H ^ (d * t) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp p * (Real.exp p) ^ (d * t) :=
      mul_le_mul hB (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _) (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (p + (d * t : ℕ) * p) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hdt : (d : ℝ) * t ≤ p * p :=
        mul_le_mul hd ht (Nat.cast_nonneg _) hp
      have hmul := mul_le_mul_of_nonneg_right hdt hp
      push_cast
      nlinarith only [hp, hmul, sq_nonneg p]

namespace RationalFilteredNilmanifold

variable {L V : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
  {s d t : ℕ} (E : RationalFilteredNilmanifold L s d) (e : Basis (Fin t) ℚ V)
  (φ : V →ₗ[ℚ] L)

theorem exists_direction_lattice_scale {H : ℕ}
    (hφ : ∀ i j, RationalHeightLE (E.basis.repr (φ (e i)) j) H) :
    ∃ m : ℕ, 0 < m ∧ m ≤ E.grid * H ^ (d * t) ∧
      ∀ x : V, IntegralVector (e.equivFun x) →
        (⟨(m : ℚ) • φ x⟩ : E.filtration.Group) ∈ E.lattice := by
  classical
  let A := LinearMap.toMatrix e E.basis φ
  let m := E.grid * matrixDenominator A
  have hA : ∀ j i, RationalHeightLE (A j i) H := by
    intro j i
    simpa only [A, LinearMap.toMatrix_apply] using hφ i j
  have hm : m ≤ E.grid * H ^ (d * t) := by
    exact Nat.mul_le_mul_left _ (by simpa only [Fintype.card_fin] using matrixDenominator_le A hA)
  refine ⟨m, Nat.mul_pos E.grid_pos (matrixDenominator_pos A), hm, ?_⟩
  intro x hx
  apply (bchSubgroupCoordinates_repr E.basis E.lattice _).mp
  apply E.inner_grid
  have he : A *ᵥ e.equivFun x = E.basis.equivFun (φ x) :=
    LinearMap.toMatrix_mulVec_repr e E.basis φ x
  have hint := integralVector_denominator_mulVec A (e.equivFun x) hx
  rw [he] at hint
  obtain ⟨z, hz⟩ := hint
  refine ⟨z, ?_⟩
  change E.basis.equivFun ((m : ℚ) • φ x) = _
  calc
    _ = (E.grid : ℚ) • ((matrixDenominator A : ℚ) • E.basis.equivFun (φ x)) := by
      simp only [m, Nat.cast_mul, map_smul, mul_smul]
    _ = _ := congrArg (fun v : Fin d → ℚ => (E.grid : ℚ) • v) (funext hz)

theorem exists_direction_lattice_scale_with_budget {H : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hgrid : (E.grid : ℝ) ≤ Real.exp p) (hH : (H : ℝ) ≤ Real.exp p)
    (hφ : ∀ i j, RationalHeightLE (E.basis.repr (φ (e i)) j) H) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
      ∀ x : V, IntegralVector (e.equivFun x) →
        (⟨(m : ℚ) • φ x⟩ : E.filtration.Group) ∈ E.lattice := by
  obtain ⟨m, hm, hmb, hmem⟩ := E.exists_direction_lattice_scale e φ hφ
  exact ⟨m, hm, (Nat.cast_le.mpr hmb).trans
    (direction_lattice_scale_bound d t E.grid H hp hd ht hgrid hH), hmem⟩

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r k d : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (E : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) k d)

theorem exists_marked_direction_lattice_scale {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (ht : (t : ℝ) ≤ p) (hgrid : (E.grid : ℝ) ≤ Real.exp p)
    (hdir : ∀ i j, rationalLogHeight
      (E.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤ p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 3) ^ 3) ∧
      ∀ a : Fin t → ℤ,
        (⟨(m : ℚ) • markedQuotientDirection F v w marked t (fun i => (a i : ℚ))⟩ :
          E.filtration.Group) ∈ E.lattice := by
  have hp1 : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  obtain ⟨m, hm, hmb, hmem⟩ := E.exists_direction_lattice_scale_with_budget (RationalTorus.basis t)
    (markedQuotientDirectionLinear F v w marked t)
    (p := p + 1) (hp.trans hp1) (hd.trans hp1) (ht.trans hp1)
    (hgrid.trans (Real.exp_le_exp.mpr hp1)) (ceil_exp_le_exp_add_one hp)
    (fun i j => rationalHeightLE_ceil_exp (hdir i j))
  refine ⟨m, hm, ?_, ?_⟩
  · simpa only [add_assoc, show (1 : ℝ) + 2 = 3 by norm_num] using hmb
  · intro a
    exact hmem (fun i => (a i : ℚ))
      ⟨a, fun i => congrFun (RationalTorus.basis_equivFun t (fun j => (a j : ℚ))) i⟩

end Erdos3

end

end OAI
