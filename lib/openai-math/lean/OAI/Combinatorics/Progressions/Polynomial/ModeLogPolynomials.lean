import OAI.Combinatorics.Progressions.Linear.ModeRankLogBudget

namespace OAI

section

namespace Erdos3

open Polynomial
open scoped BigOperators

noncomputable def modeProfileLogPolynomial : Polynomial ℕ := 5 * X + C modeProfileBound + 4

noncomputable def modeBiasLogPolynomial (m : ℕ) : Polynomial ℕ :=
  C (finiteLayerInverseConstant m) + C (finiteLayerInverseExponent m) * (C (2 ^ m) * (X + 2))

noncomputable def modeShrinkLogPolynomial (m : ℕ) : Polynomial ℕ :=
  C m + modeProfileLogPolynomial + 3 * X + 4

noncomputable def modeSideLogPolynomial (m : ℕ) : Polynomial ℕ :=
  (X + modeShrinkLogPolynomial m + modeBiasLogPolynomial m + 1) + (X + modeProfileLogPolynomial + 3) + 2

noncomputable def modeRankLogPolynomial (m : ℕ) : Polynomial ℕ :=
  C m + 1 + ∑ i : Fin m,
    ((C (i.val + 1).factorial + X + C (i.val + 1) * X) +
      X ^ (i.val + 1) * (modeBiasLogPolynomial m + C (i.val + 1) * X) +
      (C (i.val + 1) * X + C (i.val + 1) * (modeShrinkLogPolynomial m + 2) + modeBiasLogPolynomial m) + 2)

theorem modeProfileLogPolynomial_eval (P : ℝ) :
    modeProfileLogPolynomial.eval₂ (Nat.castRingHom ℝ) P = modeProfileLog P := by
  simp [modeProfileLogPolynomial, modeProfileLog]

theorem modeBiasLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeBiasLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeBiasLog m P := by
  simp [modeBiasLogPolynomial, modeBiasLog, finiteLayerInverseLog, Polynomial.eval₂_pow]

theorem modeShrinkLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeShrinkLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeShrinkLog m P := by
  simp [modeShrinkLogPolynomial, modeShrinkLog, modeProfileLogPolynomial_eval]

theorem modeSideLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeSideLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeSideLog m P := by
  simp [modeSideLogPolynomial, modeSideLog, modeProfileLogPolynomial_eval,
    modeBiasLogPolynomial_eval, modeShrinkLogPolynomial_eval]

theorem modeRankLogPolynomial_eval (m : ℕ) (P : ℝ) :
    (modeRankLogPolynomial m).eval₂ (Nat.castRingHom ℝ) P = modeRankLog m P := by
  simp [modeRankLogPolynomial, modeRankLog, Polynomial.eval₂_finsetSum,
    modeBiasLogPolynomial_eval, modeShrinkLogPolynomial_eval]

theorem exists_mode_threshold_exp_budget (m : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F D S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ D → D ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeRemovalSideThreshold m d D S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F D S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget (modeSideLogPolynomial m + modeRankLogPolynomial m)
  refine ⟨K, hK, ?_⟩
  intro n d P F D S ρ ε hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP
  have hp : modeSideLog m P + modeRankLog m P ≤ (P + K) ^ K := by
    simpa only [Polynomial.eval₂_add, modeSideLogPolynomial_eval, modeRankLogPolynomial_eval] using hpoly P hP
  have hs := modeSideLog_nonneg m hP
  have hr := modeRankLog_nonneg m hP
  constructor
  · exact (modeRemovalSideThreshold_le_exp m d hP hd hD hDP hS hSP hρ hρP hε hεP).trans
      (Real.exp_le_exp.mpr (by linarith))
  · exact (modeRemovalRankThreshold_le_exp m n d hP hn hd hF hFP hD hDP hS hSP hρ hρP hε hεP).trans
      (Real.exp_le_exp.mpr (by linarith))

end Erdos3

end

end OAI
