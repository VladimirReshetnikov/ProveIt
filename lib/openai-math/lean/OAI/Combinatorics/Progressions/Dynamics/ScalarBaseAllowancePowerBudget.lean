import OAI.Combinatorics.Progressions.Polynomial.AllocatedNestedDegreeInduction

namespace OAI

section

namespace Erdos3.VectorPolynomial

private theorem shifted_source_power_le {p : ℝ} (hp : 2 ≤ p) (H C : ℕ) :
    ((p + 2) ^ H + 2) ^ C ≤ (p + 2) ^ ((H + 1) * C) := by
  have hb : 1 ≤ (p + 2) ^ H := one_le_pow₀ (by linarith)
  have hshift : (p + 2) ^ H + 2 ≤ (p + 2) ^ (H + 1) := by
    rw [pow_succ']
    nlinarith
  calc
    _ ≤ ((p + 2) ^ (H + 1)) ^ C := pow_le_pow_left₀ (by positivity) hshift C
    _ = _ := (pow_mul _ _ _).symm

theorem exists_scalarBaseAllowance_power
    (s exponent innerDepth basePower shapePower nativeC lowerExponent : ℕ) :
    ∃ H : ℕ, 1 ≤ H ∧ basePower ≤ H ∧ (shapePower + 1) * nativeC ≤ H ∧
      lowerExponent ≤ H ∧ ∀ {p : ℝ}, 2 ≤ p →
        (((p + 2) ^ shapePower + 2) ^ nativeC ≤ (p + 2) ^ H) ∧
        candidateDegreeReturnBudget s
          (candidateNestedForwardSeed exponent
            AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * s)
            ((p + 2) ^ basePower)) ≤ (p + 2) ^ H := by
  obtain ⟨Creturn, _, hReturn⟩ := exists_candidateNestedDegreeReturn_power_budget
    s exponent AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth
  let H := 1 + basePower + (shapePower + 1) * nativeC + lowerExponent +
    (basePower + 1) * Creturn
  have hbase : basePower ≤ H := by dsimp only [H]; omega
  have hshape : (shapePower + 1) * nativeC ≤ H := by dsimp only [H]; omega
  have hlower : lowerExponent ≤ H := by dsimp only [H]; omega
  have hreturn : (basePower + 1) * Creturn ≤ H := by dsimp only [H]; omega
  refine ⟨H, by dsimp only [H]; omega, hbase, hshape, hlower, ?_⟩
  intro p hp
  have hpone : 1 ≤ p + 2 := by linarith
  refine ⟨(shifted_source_power_le hp shapePower nativeC).trans
    (pow_le_pow_right₀ hpone hshape), ?_⟩
  exact (hReturn (by positivity : 0 ≤ (p + 2) ^ basePower)).trans
    ((shifted_source_power_le hp basePower Creturn).trans
      (pow_le_pow_right₀ hpone hreturn))

theorem exists_scalarBaseAllowance_power_of_le
    (s exponent innerDepth basePower shapePower nativeC lowerExponent : ℕ) :
    ∃ H : ℕ, 1 ≤ H ∧ basePower ≤ H ∧ (shapePower + 1) * nativeC ≤ H ∧
      lowerExponent ≤ H ∧ ∀ {p shape : ℝ}, 2 ≤ p →
        0 ≤ shape → shape ≤ (p + 2) ^ shapePower →
        (shape + 2) ^ nativeC ≤ (p + 2) ^ H ∧
        candidateDegreeReturnBudget s
          (candidateNestedForwardSeed exponent
            AllocatedExternalCandidateSampler.degreeSourceCountConstants innerDepth (2 * s)
            ((p + 2) ^ basePower)) ≤ (p + 2) ^ H := by
  obtain ⟨H, hH, hbase, hshape, hlower, hbound⟩ :=
    exists_scalarBaseAllowance_power s exponent innerDepth basePower shapePower nativeC lowerExponent
  refine ⟨H, hH, hbase, hshape, hlower, ?_⟩
  intro p shape hp hshape0 hshapeBound
  exact ⟨(pow_le_pow_left₀ (by linarith : 0 ≤ shape + 2)
    (add_le_add hshapeBound (le_refl (2 : ℝ))) nativeC).trans (hbound hp).1, (hbound hp).2⟩

end Erdos3.VectorPolynomial

end

end OAI
