/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem blockMonomial_lie_coefficient [DecidableEq ι] [DecidableEq σ] (π : ι → σ) (a b : σ → ℕ)
    (x y : L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv ⁅blockMonomial π a x, blockMonomial π b y⁆ c =
      Fintype.card (SquarefreeSplit π c a b) • ⁅x, y⁆ := by
  classical
  rw [squarefree_lie_coefficient]
  simp only [blockMonomial_coefficient]
  have hterm (u v : SquarefreeIndex ι) :
      (if u.val + v.val = c.val then
        ⁅if blockDegree π u.val = a then x else 0,
          if blockDegree π v.val = b then y else 0⁆ else 0) =
      if u.val + v.val = c.val ∧ blockDegree π u.val = a ∧ blockDegree π v.val = b
        then ⁅x, y⁆ else 0 := by
    by_cases hs : u.val + v.val = c.val <;>
      by_cases hu : blockDegree π u.val = a <;>
      by_cases hv : blockDegree π v.val = b <;> simp [hs, hu, hv]
  simp_rw [hterm]
  rw [← Fintype.sum_prod_type']
  rw [Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const]

theorem blockMonomial_lie (π : ι → σ) (a b : σ → ℕ) (x y : L) :
    ⁅blockMonomial π a x, blockMonomial π b y⁆ =
      blockSplitMultiplicity a b • blockMonomial π (a + b) ⁅x, y⁆ := by
  classical
  apply squarefreePolynomialEquiv.injective
  ext c
  rw [blockMonomial_lie_coefficient, map_nsmul, Pi.smul_apply, blockMonomial_coefficient]
  by_cases hc : blockDegree π c.val = a + b
  · rw [ite_eq_left hc, card_squarefreeSplit π c a b hc]
  · have hz : Fintype.card (SquarefreeSplit π c a b) = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun p => hc (squarefreeSplit_degree π c a b p)⟩
    rw [hz, zero_smul, ite_eq_right hc, smul_zero]

theorem factorialBlockMonomial_lie (π : ι → σ) (a b : σ → ℕ) (x y : L) :
    ⁅factorialBlockMonomial π a x, factorialBlockMonomial π b y⁆ =
      factorialBlockMonomial π (a + b) ⁅x, y⁆ := by
  simp only [factorialBlockMonomial, LinearMap.smul_apply, smul_lie, lie_smul, blockMonomial_lie]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul]
  have h := congrArg (fun n : ℕ => (n : ℚ)) (multidegreeFactorial_split a b)
  simp only [Nat.cast_mul] at h
  rw [mul_comm (multidegreeFactorial b : ℚ) (multidegreeFactorial a : ℚ), h]

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem blockLayerMap_lie (a b : σ → ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0)
    (x : F.layer a) (y : F.layer b) :
    ⁅F.blockLayerMap π a ha x, F.blockLayerMap π b hb y⁆ =
      F.blockLayerMap π (a + b) hab ⟨⁅x.val, y.val⁆, F.lie_mem x.property y.property⟩ := by
  apply Subtype.ext
  exact factorialBlockMonomial_lie π a b x.val y.val

end Erdos3.MultidegreeLieFiltration

end

end OAI
