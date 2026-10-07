import OAI.Combinatorics.Progressions.Nilpotent.BCHDenominatorBudget

namespace OAI

section

namespace Erdos3

open MvPolynomial Module

variable {ι X R L : Type*} [Fintype ι] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]

theorem lie_coordinate_formula_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (a b : L) (k : ι) :
    e.repr ⁅a, b⁆ k =
      ∑ ij : ι × ι, algebraMap ℚ R (c ij.1 ij.2 k) * e.repr a ij.1 * e.repr b ij.2 := by
  classical
  conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem coordinateRightBracket_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (x : X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
      (coordinateRightBracket c x p k) = e.repr ⁅a, f x⁆ k := by
  simp only [coordinateRightBracket, map_sum, map_mul, aeval_C, aeval_X, hp]
  exact (lie_coordinate_formula_over e c hc a (f x) k).symm

variable [LieAlgebra ℚ L]

theorem coordinateBracketList_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (xs : List X) (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (coordinateBracketList c xs p k) = e.repr (rightBracketList f xs a) k := by
  induction xs generalizing p a with
  | nil => exact hp k
  | cons x xs ih =>
    exact ih (coordinateRightBracket c x p) ⁅a, f x⁆
      (coordinateRightBracket_eval_over e c hc f p a hp x)

theorem dynkinCoordinatePolynomial_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (w : FreeSemigroup X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (dynkinCoordinatePolynomial c w k) =
      e.repr (dynkinWord f w) k := by
  apply coordinateBracketList_eval_over e c hc
  intro i
  simp only [aeval_X]

variable [IsScalarTower ℚ R L]

theorem bchCoordinatePolynomial_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (s : ℕ) (a b : L) (k : ι) :
    aeval (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2)
      (bchCoordinatePolynomial c s k) = e.repr (lieBCH s a b) k := by
  change _ = e.coord k (lieBCH s a b)
  rw [lieBCH_bracket_formula]
  simp only [bchCoordinatePolynomial, map_sum, map_mul, aeval_C,
    dynkinCoordinatePolynomial_eval_over e c hc,
    LinearMap.map_smul_of_tower, Algebra.smul_def, Basis.coord_apply]

theorem exists_bch_coordinate_polynomials_over_exp_height (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (e : Basis ι R L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ),
      (∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      ∃ P : ι → MvPolynomial (Fin 2 × ι) ℚ,
        (∀ (a b : L) k,
          aeval (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2) (P k) =
            e.repr (lieBCH s a b) k) ∧
        (∀ k, (P k).totalDegree ≤ s) ∧
        ∀ k m, (((P k).coeff m).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          (((P k).coeff m).den : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_bchCoordinateHeight_exp_budget s
  refine ⟨C, hC, ?_⟩
  intro e c H p hstructure hp hd hH hc
  refine ⟨bchCoordinatePolynomial c s,
    bchCoordinatePolynomial_eval_over e c hstructure s, bchCoordinatePolynomial_totalDegree c s, ?_⟩
  intro k m
  have hheight := bchCoordinatePolynomial_height c hc s k m
  have hbound := hbudget (Fintype.card ι) H p hp hd hH
  constructor
  · exact (Nat.cast_le.mpr hheight.1).trans hbound
  · exact (Nat.cast_le.mpr hheight.2).trans hbound

end Erdos3

end

end OAI
