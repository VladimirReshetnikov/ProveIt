import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3

theorem exists_mass_bounded_shear_parameter_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d D : ℕ) (M p : ℝ),
      0 ≤ p → 0 ≤ M → M ≤ p → (d : ℝ) ≤ p → D ≤ d * (d + 1) ^ s →
      ∃ t : ℝ, 0 ≤ t ∧
        (D + s.factorial + 2 * s + 1 : ℕ) ≤ t ∧
        t + shearKernelLogBudget s d M p + shearActionLogBudget s d M + (t + a) ^ a + 4 ≤
          (p + 2) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := 1 + X + Polynomial.C (s.factorial + 2 * s + 1) + X * (X + 1) ^ s
  let K := Q + Q + Q + Polynomial.C s +
    (Polynomial.C s * Q * Q + 1) * (Polynomial.C s * (Q + 1))
  let T := Polynomial.C s + Polynomial.C s *
    (Q * (Polynomial.C (s + 1) * (Q + 1) ^ s) * Polynomial.C s) +
    Polynomial.C s * (Polynomial.C s * Q * Q)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget
    (Q + K + T + (Q + Polynomial.C a) ^ a + 4)
  refine ⟨C, hC, ?_⟩
  intro d D M p hp hM hMp hd hD
  let t : ℝ := 1 + p + (s.factorial + 2 * s + 1 : ℕ) + p * (p + 1) ^ s
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by
    have hprod : 0 ≤ p * (p + 1) ^ s := by positivity
    dsimp [t]
    linarith [Nat.cast_nonneg (α := ℝ) (s.factorial + 2 * s + 1)]
  have hdt := hd.trans hpt
  have hMt := hMp.trans hpt
  have hDb : (D : ℝ) ≤ p * (p + 1) ^ s := by
    apply (Nat.cast_le.mpr hD).trans
    push_cast
    gcongr
  have hgeo : ((D + s.factorial + 2 * s + 1 : ℕ) : ℝ) ≤ t := by
    dsimp [t]
    push_cast at *
    linarith
  have hK : shearKernelLogBudget s d M p ≤
      t + t + t + s + ((s : ℝ) * t * t + 1) * ((s : ℝ) * (t + 1)) := by
    unfold shearKernelLogBudget
    push_cast
    gcongr
  have hT : shearActionLogBudget s d M ≤
      s + (s : ℝ) * (t * (((s : ℝ) + 1) * (t + 1) ^ s) * s) +
        s * ((s : ℝ) * t * t) := by
    unfold shearActionLogBudget
    push_cast
    gcongr
  have htotal : t +
      (t + t + t + s + ((s : ℝ) * t * t + 1) * ((s : ℝ) * (t + 1))) +
      (s + (s : ℝ) * (t * (((s : ℝ) + 1) * (t + 1) ^ s) * s) +
        s * ((s : ℝ) * t * t)) + (t + a) ^ a + 4 ≤ (p + 2) ^ C := by
    simpa [X, Q, K, T, t, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul] using hbound p hp
  refine ⟨t, ht, hgeo, ?_⟩
  linarith

end Erdos3

end

end OAI
