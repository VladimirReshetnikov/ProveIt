import OAI.Combinatorics.Progressions.Polynomial.GlobalAffineDegreeChoice

namespace OAI

section

namespace Erdos3

noncomputable def adaptiveAffineCountLog (A sourceDim siteDim : ℕ)
    (ε L T C modLog : ℝ) : ℝ :=
  (A : ℝ) * (affineComparisonScale ε L T C +
    (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1)

noncomputable def adaptiveAffineShell (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog : ℝ) : ℝ :=
  totalShell * Real.exp (-adaptiveAffineCountLog A sourceDim siteDim ε L T C modLog)

noncomputable def adaptiveAffineCutoff (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog : ℝ) : ℕ :=
  affineGlobalComparisonDegree A sourceDim siteDim ε L T C
    (adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog) modLog 0

noncomputable def adaptiveAffineSideLog (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog dimLog : ℝ) : ℝ :=
  modLog * A + affineComparisonLengthLog
    (adaptiveAffineCutoff A sourceDim siteDim ε L T C totalShell modLog)
    ε L T C modLog dimLog + 2

theorem adaptiveAffineCountLog_nonneg (A sourceDim siteDim : ℕ)
    {ε L T C modLog : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmodLog : 0 ≤ modLog) :
    0 ≤ adaptiveAffineCountLog A sourceDim siteDim ε L T C modLog := by
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  unfold adaptiveAffineCountLog
  positivity

theorem adaptiveAffineShell_pos (A sourceDim siteDim : ℕ)
    (ε L T C modLog : ℝ) {totalShell : ℝ} (h : 0 < totalShell) :
    0 < adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog :=
  mul_pos h (Real.exp_pos _)

theorem adaptiveAffineShell_allocation (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog : ℝ) :
    Real.exp (adaptiveAffineCountLog A sourceDim siteDim ε L T C modLog) *
      adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog = totalShell := by
  unfold adaptiveAffineShell
  rw [mul_left_comm, ← Real.exp_add]
  simp

theorem adaptiveAffineShell_le (A sourceDim siteDim : ℕ)
    {ε L T C totalShell modLog : ℝ} (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hmodLog : 0 ≤ modLog) (h : 0 ≤ totalShell) :
    adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog ≤ totalShell := by
  have hexp := Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (adaptiveAffineCountLog_nonneg (ε := ε) A sourceDim siteDim hL hT hC hmodLog))
  exact (mul_le_mul_of_nonneg_left hexp h).trans_eq (mul_one totalShell)

theorem adaptiveAffineShell_log (A sourceDim siteDim : ℕ)
    (ε L T C modLog : ℝ) {totalShell : ℝ} (h : 0 < totalShell) :
    Real.log (adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog) =
      Real.log totalShell - adaptiveAffineCountLog A sourceDim siteDim ε L T C modLog := by
  rw [adaptiveAffineShell, Real.log_mul h.ne' (Real.exp_pos _).ne', Real.log_exp]
  rfl

theorem adaptiveAffineCutoff_bounds (A sourceDim siteDim : ℕ)
    (ε L T C totalShell modLog : ℝ) :
    A + affineComparisonDegree sourceDim siteDim ε L T C
        (adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog) modLog ≤
      adaptiveAffineCutoff A sourceDim siteDim ε L T C totalShell modLog ∧
    A + CyclicCrootSisask.spectralIterations
        (adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog)
        ((A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4) ≤
      adaptiveAffineCutoff A sourceDim siteDim ε L T C totalShell modLog := by
  have h := affineGlobalComparisonDegree_bounds A sourceDim siteDim ε L T C
    (adaptiveAffineShell A sourceDim siteDim ε L T C totalShell modLog) modLog 0 le_rfl
  exact ⟨h.1, h.2.1⟩

end Erdos3

end

section

namespace Erdos3

theorem boundedPrimeFamily_log_bounds (Q : ℕ) {P : ℝ} (hQ : (Q : ℝ) ≤ Real.exp P) :
    (Fintype.card (BoundedPrime Q) : ℝ) ≤ Real.exp P ∧
      ∀ p : BoundedPrime Q, (boundedPrimePower Q p : ℝ) ≤ Real.exp P := by
  exact ⟨(Nat.cast_le.mpr (boundedPrime_card_le Q)).trans hQ,
    fun p => (Nat.cast_le.mpr (boundedPrimePower_le Q p)).trans hQ⟩

theorem nat_le_two_pow_of_le_exp {Q b : ℕ} {P : ℝ}
    (hQ : (Q : ℝ) ≤ Real.exp P) (hPb : 2 * P ≤ (b : ℝ)) : Q ≤ 2 ^ b := by
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hP : P ≤ (b : ℝ) * Real.log 2 := by nlinarith
  have he : Real.exp P ≤ (2 : ℝ) ^ b := by
    calc
      _ ≤ Real.exp ((b : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hP
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact_mod_cast hQ.trans he

theorem ceil_power_dominates_twice {p : ℝ} {E : ℕ} (hp : 2 ≤ p) (hE : 2 ≤ E) :
    2 * p ≤ (⌈(p + 2) ^ E⌉₊ : ℝ) := by
  have hpow : (p + 2) ^ 2 ≤ (p + 2) ^ E := pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hE
  have hbase : 2 * p ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  exact (hbase.trans hpow).trans (Nat.le_ceil _)

theorem adaptiveAffineCutoff_captures_moduli {Q E : ℕ} {p modLog : ℝ}
    (hp : 2 ≤ p) (hE : 2 ≤ E) (hmodLog : modLog ≤ p) (hQ : (Q : ℝ) ≤ Real.exp modLog)
    (sourceDim siteDim : ℕ) (ε L T C totalShell : ℝ) :
    Q ≤ 2 ^ adaptiveAffineCutoff ⌈(p + 2) ^ E⌉₊ sourceDim siteDim ε L T C totalShell modLog := by
  have h := (adaptiveAffineCutoff_bounds ⌈(p + 2) ^ E⌉₊ sourceDim siteDim ε L T C totalShell modLog).1
  have hA : ⌈(p + 2) ^ E⌉₊ ≤ adaptiveAffineCutoff ⌈(p + 2) ^ E⌉₊ sourceDim siteDim ε L T C totalShell modLog := by omega
  have hAreal : (⌈(p + 2) ^ E⌉₊ : ℝ) ≤
      (adaptiveAffineCutoff ⌈(p + 2) ^ E⌉₊ sourceDim siteDim ε L T C totalShell modLog : ℝ) := by exact_mod_cast hA
  apply nat_le_two_pow_of_le_exp hQ
  have hpow := ceil_power_dominates_twice hp hE
  linarith

end Erdos3

end

end OAI
