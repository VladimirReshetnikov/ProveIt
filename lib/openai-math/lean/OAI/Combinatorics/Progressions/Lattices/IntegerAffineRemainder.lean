import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import OAI.Combinatorics.Progressions.Estimates.RationalRowReduction
import OAI.Combinatorics.Progressions.Estimates.ScalarExtensionSubstitution

namespace OAI

section

namespace Erdos3

open MvPolynomial

theorem exists_integer_affine_remainder {I : Type*}
    (P : MvPolynomial I ℤ) (r : I → ℤ) (a : ℤ) :
    ∃ Q : MvPolynomial I ℤ,
      aeval (fun i => C (r i) + C a * X i) P = C (eval r P) + C a * Q := by
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨0, by simp⟩
  | add P S hP hS =>
    obtain ⟨Q, hQ⟩ := hP
    obtain ⟨T, hT⟩ := hS
    refine ⟨Q + T, ?_⟩
    simp only [map_add, hQ, hT]
    ring
  | mul_X P i hP =>
    obtain ⟨Q, hQ⟩ := hP
    refine ⟨Q * (C (r i) + C a * X i) + C (eval r P) * X i, ?_⟩
    simp only [map_mul, aeval_X, eval_X, hQ]
    ring

theorem exists_integer_affine_remainder_degree {I : Type*}
    (P : MvPolynomial I ℤ) (r : I → ℤ) {a : ℤ} (ha : a ≠ 0) :
    ∃ Q : MvPolynomial I ℤ,
      aeval (fun i => C (r i) + C a * X i) P = C (eval r P) + C a * Q ∧
      Q.totalDegree ≤ P.totalDegree := by
  obtain ⟨Q, hQ⟩ := exists_integer_affine_remainder P r a
  refine ⟨Q, hQ, ?_⟩
  by_cases hQ0 : Q = 0
  · simp [hQ0]
  have hCa : (C a : MvPolynomial I ℤ) ≠ 0 := by simpa using ha
  have hprod : C a * Q = aeval (fun i => C (r i) + C a * X i) P - C (eval r P) := by
    rw [hQ]
    ring
  have hdeg : (aeval (fun i => C (r i) + C a * X i) P).totalDegree ≤ P.totalDegree := by
    have hf (i : I) : (C (r i) + C a * X i).totalDegree ≤ 1 := by
      apply (totalDegree_add _ _).trans
      simp only [max_le_iff, totalDegree_C]
      refine ⟨by omega, ?_⟩
      simpa only [totalDegree_C, totalDegree_X, zero_add] using totalDegree_mul (C a) (X i)
    simpa only [Nat.mul_one] using aeval_polynomial_totalDegree_le P _ le_rfl hf
  have hbound := (totalDegree_sub_C_le (aeval (fun i => C (r i) + C a * X i) P)
    (eval r P)).trans hdeg
  rwa [← hprod, totalDegree_mul_of_isDomain hCa hQ0, totalDegree_C, zero_add] at hbound

theorem integer_affine_remainder_eval {I : Type*}
    (P Q : MvPolynomial I ℤ) (r : I → ℤ) (a : ℤ)
    (hQ : aeval (fun i => C (r i) + C a * X i) P = C (eval r P) + C a * Q)
    (x : I → ℤ) : eval (fun i => r i + a * x i) P = eval r P + a * eval x Q := by
  have he := congrArg (aeval (R := ℤ) x) hQ
  rw [comp_aeval_apply] at he
  simpa only [map_add, map_mul, aeval_C, aeval_X, Algebra.algebraMap_self,
    RingHom.id_apply, aeval_eq_eval] using he

theorem exists_rational_affine_integer_remainder {I J : Type*} [Fintype J]
    (P : MvPolynomial I ℤ) (e : J → ℚ) {H : ℕ}
    (he : ∀ i, RationalHeightLE (e i) H) :
    ∃ d : ℕ, 0 < d ∧ d ≤ H ^ Fintype.card J ∧
      ∀ D : ℕ, 0 < D → ∀ r : I → ℤ, ∃ Q : J → MvPolynomial I ℤ,
        (∀ i, (Q i).totalDegree ≤ P.totalDegree) ∧
        ∀ (x : I → ℤ) (i : J),
          (eval (fun j => r j + (D * d : ℕ) * x j) P : ℝ) / D * (e i : ℝ) =
            (eval r P : ℝ) / D * (e i : ℝ) + (eval x (Q i) : ℝ) := by
  classical
  obtain ⟨d, hd, hdH, z, hz, _⟩ := exists_bounded_integer_array e he
  refine ⟨d, hd, hdH, ?_⟩
  intro D hD r
  have ha : ((D * d : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hD hd).ne'
  obtain ⟨Q, hQ, hdegree⟩ := exists_integer_affine_remainder_degree P r ha
  refine ⟨fun i => C (z i) * Q, ?_, ?_⟩
  · intro i
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, zero_add] using hdegree)
  · intro x i
    have hvalue := integer_affine_remainder_eval P Q r ((D * d : ℕ) : ℤ) hQ x
    have hvalueR : (eval (fun j => r j + (D * d : ℕ) * x j) P : ℝ) =
        (eval r P : ℝ) + (D : ℝ) * d * (eval x Q : ℝ) := by exact_mod_cast hvalue
    have hzi : (z i : ℝ) = (d : ℝ) * (e i : ℝ) := by
      exact_mod_cast hz i
    rw [hvalueR, map_mul, eval_C, Int.cast_mul, hzi]
    have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    field_simp

end Erdos3

end

end OAI
