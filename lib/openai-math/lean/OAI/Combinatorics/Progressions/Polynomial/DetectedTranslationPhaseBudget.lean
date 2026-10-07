import OAI.Combinatorics.Progressions.Geometry.DetectedTranslationCoordinateBudget
import OAI.Combinatorics.Progressions.Geometry.TranslationCoordinateBudget

namespace OAI

section

namespace Erdos3

theorem exists_detectedTranslationPhase_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n t k b m q : ℕ) (p H A : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → (t : ℝ) ≤ p → (k : ℝ) ≤ p →
      (b : ℝ) ≤ p → 0 ≤ H → H ≤ Real.exp p →
      0 ≤ A → A ≤ Real.exp p → (m : ℝ) ≤ Real.exp p →
      q ≤ ⌈Real.exp p⌉₊ ^ (t * k) * m →
      let Z : ℝ := ((n : ℝ) + 1) ^ d * k * H * A
      Z ≤ Real.exp ((p + C) ^ C) ∧
      ((d : ℝ) + 1) * ((t : ℝ) * Z) *
          (1 + (b : ℝ) * d * t * Z) ^ d ≤ Real.exp ((p + C) ^ C) ∧
      (d.factorial * q ^ (d + 1) : ℕ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨a, _, hcoordinate⟩ := exists_translationCoordinate_budget d
  let S : Polynomial ℕ :=
    Polynomial.C (d + 3) * (Polynomial.X + 1) + (Polynomial.X + 3) ^ 3
  let Q : Polynomial ℕ := S + (S + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro n t k b m q p H A hp hn ht hk hb hH hHp hA hAp hm hq
  let Z : ℝ := ((n : ℝ) + 1) ^ d * k * H * A
  let s : ℝ := ((d : ℝ) + 3) * (p + 1) + (p + 3) ^ 3
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hsbudget : s + (s + a) ^ a ≤ (p + C) ^ C := by
    simpa [Q, S, s, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  have hsp : p ≤ s := by
    dsimp [s]
    have hdp := mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hp
    have hc : 0 ≤ (p + 3) ^ 3 := by positivity
    nlinarith
  have hsZ : ((d : ℝ) + 3) * p + d ≤ s := by
    dsimp [s]
    have hc : 0 ≤ (p + 3) ^ 3 := by positivity
    nlinarith
  have hsq : (p + 3) ^ 3 ≤ s := by
    exact le_add_of_nonneg_left (by positivity)
  have hnp : (n : ℝ) + 1 ≤ Real.exp (p + 1) := by
    linarith [Real.add_one_le_exp (p + 1)]
  have hkp : (k : ℝ) ≤ Real.exp p := hk.trans (by linarith [Real.add_one_le_exp p])
  have hZ : Z ≤ Real.exp s := by
    apply le_trans _ (Real.exp_le_exp.mpr hsZ)
    calc
      Z ≤ Real.exp (p + 1) ^ d * Real.exp p * Real.exp p * Real.exp p := by
        dsimp [Z]
        gcongr
      _ = Real.exp (((d : ℝ) + 3) * p + d) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hqexp : (q : ℝ) ≤ Real.exp s :=
    (detectedTranslationCoordinate_denominator_le_exp t k m q hp ht hk hm hq).trans
      (Real.exp_le_exp.mpr hsq)
  have hts : (t : ℝ) ≤ Real.exp s :=
    (ht.trans hsp).trans (by linarith [Real.add_one_le_exp s])
  have hZ0 : 0 ≤ Z := by dsimp [Z]; positivity
  obtain ⟨hmass, hdenom⟩ := hcoordinate b t q s Z 1 hs (hb.trans hsp) hts
    hZ0 hZ zero_le_one (Real.one_le_exp_iff.mpr hs) hqexp
  have hpow : (s + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left hs).trans hsbudget
  have hsle : s ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) a)).trans hsbudget
  refine ⟨hZ.trans (Real.exp_le_exp.mpr hsle), ?_, hdenom.trans (Real.exp_le_exp.mpr hpow)⟩
  have hmass' := hmass.trans (Real.exp_le_exp.mpr hpow)
  simpa only [Z, mul_one, mul_assoc] using hmass'

end Erdos3

end

end OAI
