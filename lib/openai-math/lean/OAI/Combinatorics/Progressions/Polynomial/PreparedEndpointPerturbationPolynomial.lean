import OAI.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedSourceErrorBudget

namespace OAI

section

namespace Erdos3

theorem exists_preparedEndpointPerturbation_budget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {t D primitiveCap Ptest Ecompare cost : ℝ},
      0 ≤ t → D ∈ Set.Icc 0 t → primitiveCap ∈ Set.Icc 0 t →
      Ptest ∈ Set.Icc 0 t → Ecompare ∈ Set.Icc 0 t → cost ∈ Set.Icc 0 t →
      let sourceLog := 2 + D ^ 2 + primitiveCap + max 0 Ptest
      fixedPathSlicedPerturbationLog D (D + sourceLog + 4) (cost + 1)
          (2 * sourceLog + Ecompare + 18) m ∈ Set.Icc 0 ((t + C) ^ C) ∧
        2 * sourceLog + Ecompare + 18 ∈ Set.Icc 0 ((t + C) ^ C) := by
  let Lpoly : Polynomial ℕ := 2 + Polynomial.X ^ 2 + 2 * Polynomial.X
  let Epoly : Polynomial ℕ := 2 * Lpoly + Polynomial.X + 18
  let Qpoly : Polynomial ℕ := 4 * Polynomial.X + 3 * Lpoly + Polynomial.C m + 25
  let Tpoly : Polynomial ℕ :=
    48 * ((3 * Qpoly + 4) * Polynomial.C m + 5 * Qpoly + 10) +
      2 * Qpoly + 2 * Polynomial.C m + 47
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (Tpoly + Epoly)
  refine ⟨C, hC, ?_⟩
  intro t D primitiveCap Ptest Ecompare cost ht hD hprimitive htest hcompare hcost
  let sourceLog := 2 + D ^ 2 + primitiveCap + max 0 Ptest
  let L := 2 + t ^ 2 + 2 * t
  let E := 2 * L + t + 18
  let Q := 4 * t + 3 * L + m + 25
  let T := 48 * ((3 * Q + 4) * m + 5 * Q + 10) + 2 * Q + 2 * m + 47
  have hsource : 0 ≤ sourceLog := by
    dsimp only [sourceLog]
    exact add_nonneg (add_nonneg (by positivity) hprimitive.1) (le_max_left _ _)
  have hsourceL : sourceLog ≤ L := by
    have hsquare := pow_le_pow_left₀ hD.1 hD.2 2
    dsimp only [sourceLog, L]
    rw [max_eq_right htest.1]
    linarith only [hsquare, hprimitive.2, htest.2]
  have hE : 0 ≤ E := by dsimp only [E, L]; positivity
  have hT : 0 ≤ T := by dsimp only [T, Q, L]; positivity
  have hcoarse : 0 ≤ 2 * sourceLog + Ecompare + 18 := by
    linarith only [hsource, hcompare.1]
  have hcoarseE : 2 * sourceLog + Ecompare + 18 ≤ E := by
    dsimp only [E]
    linarith only [hsourceL, hcompare.2]
  have hQ : D + ((D + sourceLog + 4) + (cost + 1)) +
      (2 * sourceLog + Ecompare + 18) + m + 2 ≤ Q := by
    dsimp only [Q]
    linarith only [hsourceL, hD.2, hcost.2, hcompare.2]
  have hQm := mul_le_mul_of_nonneg_right hQ (Nat.cast_nonneg (α := ℝ) m)
  have hperturb : fixedPathSlicedPerturbationLog D (D + sourceLog + 4) (cost + 1)
      (2 * sourceLog + Ecompare + 18) m ≤ T := by
    dsimp only [fixedPathSlicedPerturbationLog, fixedPathPerturbationLog, T]
    nlinarith only [hQ, hQm]
  have htotal : T + E ≤ (t + C) ^ C := by
    simpa [Tpoly, Epoly, Qpoly, Lpoly, T, Q, E, L] using hbound t ht
  exact ⟨⟨fixedPathSlicedPerturbationLog_nonneg hD.1
      (by linarith only [hD.1, hsource]) (by linarith only [hcost.1]) hcoarse m,
      hperturb.trans ((le_add_of_nonneg_right hE).trans htotal)⟩,
    ⟨hcoarse, hcoarseE.trans ((le_add_of_nonneg_left hT).trans htotal)⟩⟩

end Erdos3

end

end OAI
