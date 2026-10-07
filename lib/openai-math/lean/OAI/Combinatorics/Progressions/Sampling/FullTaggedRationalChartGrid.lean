/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.FullTaggedRationalRetraction

namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical Matrix

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedLinearMapChart_coefficientGrid
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (D : ℕ)
    (hP : ∀ j i a, ∃ z : ℤ, (D : ℝ) * P j (Pi.single a 1) i = (z : ℝ))
    (v : X ⊕ (Σ j, J j)) :
    realPolynomialCoefficientGrid D (fullTaggedLinearMapChart J P v) := by
  cases v with
  | inl x => exact realPolynomialCoefficientGrid_X D _
  | inr v =>
    apply (realPolynomialCoefficientGrid_iff D _).mpr
    change C (D : ℝ) * (∑ a : J v.1, P v.1 (Pi.single a 1) v.2 •
      MvPolynomial.X (Sum.inr ⟨v.1, a⟩ : X ⊕ (Σ j, J j))) ∈
        integralRealPolynomialSubring (X ⊕ (Σ j, J j))
    simp only [smul_eq_C_mul, Finset.mul_sum]
    apply (integralRealPolynomialSubring _).sum_mem
    intro a _
    obtain ⟨z, hz⟩ := hP v.1 v.2 a
    rw [← mul_assoc, ← map_mul, hz]
    exact (integralRealPolynomialSubring _).mul_mem
      (C_int_mem_integralRealPolynomialSubring z) (X_mem_integralRealPolynomialSubring _)

theorem exists_fullTaggedRationalChart_common_grid
    (P : ∀ j, Matrix (J j) (J j) ℚ) (D : Fin m → ℕ)
    (hD : ∀ j, 0 < D j) {B : ℝ} (hDB : ∀ j, (D j : ℝ) ≤ Real.exp B)
    (hclear : ∀ j i a, ∃ z : ℤ, (D j : ℝ) * (P j i a : ℝ) = (z : ℝ)) :
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp ((m : ℝ) * B) ∧
      (∀ j, D j ∣ d) ∧
      ∀ (c : ∀ j, J j → ℝ) (v : X ⊕ (Σ j, J j)),
        realPolynomialCoefficientGrid d
          (weightedHomogeneousComponent (fullTaggedVariableWeight J)
            (fullTaggedVariableWeight J v)
            (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J P) c v)) := by
  let d := ∏ j, D j
  have hdiv (j : Fin m) : D j ∣ d := Finset.dvd_prod_of_mem D (Finset.mem_univ j)
  have hd : 0 < d := Finset.prod_pos (fun j _ => hD j)
  have hdB : (d : ℝ) ≤ Real.exp ((m : ℝ) * B) := by
    dsimp only [d]
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _j : Fin m, Real.exp B :=
        Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hDB j)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
  refine ⟨d, hd, hdB, hdiv, ?_⟩
  intro c v
  rw [fullTaggedAffineMapChart_top]
  apply fullTaggedLinearMapChart_coefficientGrid J (fullTaggedRealMatrixProjection J P) d
  intro j i a
  obtain ⟨z, hz⟩ := hclear j i a
  obtain ⟨k, hk⟩ := hdiv j
  refine ⟨(k : ℤ) * z, ?_⟩
  have hentry : fullTaggedRealMatrixProjection J P j (Pi.single a 1) i = (P j i a : ℝ) := by
    change (Matrix.mulVecLin (fun (i a : J j) => (P j i a : ℝ)))
      (Pi.single a (1 : ℝ)) i = (P j i a : ℝ)
    exact congrFun (Matrix.mulVec_single_one (fun (i a : J j) => (P j i a : ℝ)) a) i
  rw [hentry, hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← hz]
  ring

end Erdos3.VectorPolynomial

end

end OAI
