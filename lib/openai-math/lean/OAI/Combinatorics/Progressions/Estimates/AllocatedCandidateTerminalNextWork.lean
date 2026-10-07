import OAI.Combinatorics.Progressions.Dynamics.CandidatePhysicalOrdinaryBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_allocatedCandidateTerminalFullInput_forward_budget
    (s m Cprimitive A : ℕ) (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      allocatedCandidateTerminalFullInput s m Cprimitive x
        (preparedFiniteForwardWork A stageCountConstant s x)
        (preparedFiniteForwardCumulative A stageCountConstant s x) ≤ (x + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let cumulative : Polynomial ℕ :=
    ∑ j ∈ Finset.range s, preparedFiniteForwardCapPolynomial A stageCountConstant j
  let Q : Polynomial ℕ := cumulative + ((cumulative + 2) ^ 2 + 2) ^ 63
  let B : Polynomial ℕ := 2 * cumulative + (Q + 2) ^ 10 + (Q + 2) ^ 8 + 1
  let P : Polynomial ℕ :=
    (X + Polynomial.C Cprimitive) ^ Cprimitive + X +
      preparedFiniteForwardWorkPolynomial A stageCountConstant s +
      Polynomial.C s * Polynomial.C m * B + B + Polynomial.C s + Polynomial.C m + 10
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hcumulative : cumulative.eval₂ (Nat.castRingHom ℝ) x =
      preparedFiniteForwardCumulative A stageCountConstant s x := by
    simp only [cumulative, Polynomial.eval₂_finsetSum, preparedFiniteForwardCumulative,
      preparedFiniteForwardCap]
  have hB : B.eval₂ (Nat.castRingHom ℝ) x =
      certifiedAffineCenterBudget (preparedFiniteForwardCumulative A stageCountConstant s x) := by
    simp only [B, Q, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_ofNat, Polynomial.eval₂_one, hcumulative, certifiedAffineCenterBudget]
  simpa only [P, X, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Nat.coe_castRingHom,
    hB, allocatedCandidateTerminalFullInput, preparedFiniteForwardWork] using hbudget x hx

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

private noncomputable def terminalAffinePolynomial : Polynomial ℕ :=
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + ((X + 2) ^ 2 + 2) ^ 63
  2 * X + (Q + 2) ^ 10 + (Q + 2) ^ 8 + 1

private theorem terminalAffinePolynomial_eval (x : ℝ) :
    terminalAffinePolynomial.eval₂ (Nat.castRingHom ℝ) x = certifiedAffineCenterBudget x := by
  simp only [terminalAffinePolynomial, certifiedAffineCenterBudget, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one]

private noncomputable def terminalUniformPolynomial (s m Cprimitive : ℕ) : Polynomial ℕ :=
  (Polynomial.X + Polynomial.C Cprimitive) ^ Cprimitive + Polynomial.X + Polynomial.X +
    Polynomial.C s * Polynomial.C m * terminalAffinePolynomial + terminalAffinePolynomial +
    Polynomial.C s + Polynomial.C m + 10

private theorem terminalUniformPolynomial_eval (s m Cprimitive : ℕ) (x : ℝ) :
    (terminalUniformPolynomial s m Cprimitive).eval₂ (Nat.castRingHom ℝ) x =
      allocatedCandidateTerminalFullInput s m Cprimitive x x x := by
  simp only [terminalUniformPolynomial, allocatedCandidateTerminalFullInput,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Nat.coe_castRingHom,
    terminalAffinePolynomial_eval]

attribute [local irreducible] certifiedAffineCenterBudget
  preparedFiniteForwardParameter preparedFiniteForwardWork preparedFiniteForwardCap
  preparedFiniteForwardBranch preparedFiniteForwardCumulative

private theorem terminalFullInput_le_uniform (s m Cprimitive : ℕ)
    {x work cumulative u : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ cumulative)
    (hxu : x ≤ u) (hwu : work ≤ u) (hcu : cumulative ≤ u) :
    allocatedCandidateTerminalFullInput s m Cprimitive x work cumulative ≤
      (terminalUniformPolynomial s m Cprimitive).eval₂ (Nat.castRingHom ℝ) u := by
  have hB : certifiedAffineCenterBudget cumulative ≤ certifiedAffineCenterBudget u := by
    simpa only [terminalAffinePolynomial_eval] using
      natPolynomial_eval_mono_nonneg terminalAffinePolynomial hc hcu
  rw [terminalUniformPolynomial_eval]
  unfold allocatedCandidateTerminalFullInput
  gcongr

theorem exists_allocatedCandidateTerminalFullInput_polynomial_next_work
    (s m Cprimitive : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ},
      C ≤ A → 0 ≤ x →
      P.eval₂ (Nat.castRingHom ℝ)
        (allocatedCandidateTerminalFullInput s m Cprimitive x
          (preparedFiniteForwardWork A stageCountConstant s x)
          (preparedFiniteForwardCumulative A stageCountConstant s x)) ≤
        preparedFiniteForwardWork A stageCountConstant (s + 1) x := by
  obtain ⟨C, hC, hcap⟩ := exists_preparedFiniteForward_polynomial_cap
    (P.comp (terminalUniformPolynomial s m Cprimitive))
  refine ⟨C, hC, ?_⟩
  intro A stageCountConstant x hCA hx
  have hA : 2 ≤ A := hC.trans hCA
  have hzero : (0 : ℝ) ∈ Set.Icc 0 x := ⟨le_rfl, hx⟩
  have hprec := preparedFiniteForward_model_precision_bounds A stageCountConstant s hx hzero hzero
  have hprefix := preparedFiniteForward_prefix_bounds A stageCountConstant s hx
  have hwork := preparedFiniteForward_model_scalar_bounds A stageCountConstant s 0 hA hx
    (by simpa only [Nat.cast_zero] using hx)
  let u := preparedFiniteForwardSourcePrecision A stageCountConstant s x 0 0 +
    preparedFiniteForwardWork A stageCountConstant s x
  have hwu : preparedFiniteForwardWork A stageCountConstant s x ≤ u :=
    le_add_of_nonneg_left hprec.2.1
  have hxu : x ≤ u :=
    (le_preparedFiniteForwardParameter A stageCountConstant s hx).trans (hwork.2.1.trans hwu)
  have hcu : preparedFiniteForwardCumulative A stageCountConstant s x ≤ u :=
    hprefix.1.2.trans (hwork.2.1.trans hwu)
  have hinput := terminalFullInput_le_uniform s m Cprimitive hx hprefix.1.1 hxu hwu hcu
  have hinput0 :=
    (allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hwork.1 hprefix.1.1).1
  have hP := natPolynomial_eval_mono_nonneg P hinput0 hinput
  have hcapP : P.eval₂ (Nat.castRingHom ℝ)
      ((terminalUniformPolynomial s m Cprimitive).eval₂ (Nat.castRingHom ℝ) u) ≤
        preparedFiniteForwardCap A stageCountConstant s x := by
    simpa only [Polynomial.eval₂_comp, u] using hcap A stageCountConstant s hCA hx hzero hzero
  have hnext := preparedFiniteForward_model_scalar_bounds A stageCountConstant (s + 1) 0 hA hx
    (by simpa only [Nat.cast_zero] using hx)
  have hcapNext : preparedFiniteForwardCap A stageCountConstant s x ≤
      preparedFiniteForwardParameter A stageCountConstant (s + 1) x := by
    rw [preparedFiniteForwardParameter_succ]
    have hb := preparedFiniteForwardParameter_nonneg A stageCountConstant s hx
    have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant s hx
    linarith only [hb, hbranch]
  exact (hP.trans hcapP).trans (hcapNext.trans hnext.2.1)

theorem exists_allocatedCandidateTerminalFullInput_next_work (s m Cprimitive : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (stageCountConstant : ℕ → ℕ) {x : ℝ},
      C ≤ A → 0 ≤ x →
      allocatedCandidateTerminalFullInput s m Cprimitive x
        (preparedFiniteForwardWork A stageCountConstant s x)
        (preparedFiniteForwardCumulative A stageCountConstant s x) ≤
        preparedFiniteForwardWork A stageCountConstant (s + 1) x := by
  simpa only [Polynomial.eval₂_X] using
    exists_allocatedCandidateTerminalFullInput_polynomial_next_work s m Cprimitive Polynomial.X

end Erdos3.VectorPolynomial

end

end OAI
