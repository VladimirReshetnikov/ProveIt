import OAI.Combinatorics.Progressions.Probability.TranslatedSelectedDensityCap

namespace OAI

section

namespace Erdos3

noncomputable def selectedCollisionLog (m : ℕ) (P : ℝ) : ℝ :=
  selectedDensityLog m P + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4

theorem exists_selectedCollisionLog_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P → selectedCollisionLog m P ≤ (P+A)^A := by
  let a := VectorPolynomial.selectedFourierExponent m
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C a)^a + 1 +
    2*Polynomial.X*(Polynomial.X+5) + (4*Polynomial.X+128) + 2*Polynomial.X + 4
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget q
  refine ⟨A, hA, ?_⟩
  intro P hP
  simpa [q, a, selectedCollisionLog, selectedDensityLog, spatialSamplingBudget,
    Polynomial.eval₂_pow] using hbound P hP

theorem collision_error_of_exp_size (m : ℕ) {P C q ρ δ N : ℝ}
    (hC0 : 0 ≤ C) (hq0 : 0 ≤ q) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hC : C ≤ Real.exp (P*(P+5))) (hq : q ≤ Real.exp P)
    (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P)) (hδP : δ⁻¹ ≤ Real.exp P)
    (hN : Real.exp (selectedCollisionLog m P) ≤ N) :
    2*Real.exp (selectedDensityLog m P)*(C^2*(2*q/(ρ*N))) ≤ δ := by
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hmain : (4*Real.exp (selectedDensityLog m P)*C^2*q*(1/ρ))/δ ≤ N := by
    calc
      _ = 4*Real.exp (selectedDensityLog m P)*C^2*q*(1/ρ)*δ⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 4*Real.exp (selectedDensityLog m P)*
          (Real.exp (P*(P+5)))^2*Real.exp P*
          Real.exp (spatialSamplingBudget P)*Real.exp P := by gcongr
      _ = Real.exp (selectedCollisionLog m P) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_add, ← Real.exp_add]
        congr 1
        unfold selectedCollisionLog
        norm_num
        ring
      _ ≤ N := hN
  have hnum := (div_le_iff₀ hδ).mp hmain
  calc
    _ = (4*Real.exp (selectedDensityLog m P)*C^2*q*(1/ρ))/N := by ring
    _ ≤ δ := (div_le_iff₀ hN0).mpr (by simpa only [mul_comm N δ] using hnum)

end Erdos3

end

end OAI
