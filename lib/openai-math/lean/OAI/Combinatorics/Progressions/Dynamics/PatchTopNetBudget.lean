import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearObservableNet
import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3

noncomputable def patchTopNetNumerator (d s : ℕ) (M : ℝ) : ℝ :=
  ((s + 1) * (d + 1) ^ s : ℕ) * 4 * (1 + M) * ((1 + M) ^ (s * d)) ^ s

def patchTopNetNumeratorLog (s : ℕ) (p : ℝ) : ℝ :=
  s + s * p + p + 4 + s * s * p * (p + 1)

theorem patchTopNetError_eq_div (d s N : ℕ) (M : ℝ) :
    patchTopNetError d s N M = patchTopNetNumerator d s M / N := by
  unfold patchTopNetError patchTopNetNumerator
  ring

theorem patchTopNetNumeratorLog_nonneg (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ patchTopNetNumeratorLog s p := by unfold patchTopNetNumeratorLog; positivity

theorem patchTopNetNumerator_le_exp (d s : ℕ) {M p : ℝ} (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hd : (d : ℝ) ≤ p) (hMp : M ≤ Real.exp p) :
    patchTopNetNumerator d s M ≤ Real.exp (patchTopNetNumeratorLog s p) := by
  have hs : (s : ℝ) + 1 ≤ Real.exp s := Real.add_one_le_exp _
  have hd1 : (d : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hM1 : 1 + M ≤ Real.exp (p + 1) := by
    simpa only [zero_add] using add_le_exp_add_one (le_refl (0 : ℝ)) hp
      (by simp : (1 : ℝ) ≤ Real.exp 0) hMp
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  calc
    patchTopNetNumerator d s M ≤
        (Real.exp s * (Real.exp p) ^ s) * Real.exp 3 * Real.exp (p + 1) *
          ((Real.exp (p + 1)) ^ (s * d)) ^ s := by
      unfold patchTopNetNumerator
      push_cast
      gcongr
    _ = Real.exp (s + s * p + 3 + (p + 1) + s * ((s * d : ℕ) : ℝ) * (p + 1)) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold patchTopNetNumeratorLog
      push_cast
      have h := mul_le_mul_of_nonneg_left hd
        (by positivity : 0 ≤ (s : ℝ) * s * (p + 1))
      nlinarith

theorem exists_small_patch_top_mesh (d s : ℕ) {M L p : ℝ}
    (hp : 0 ≤ p) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hd : (d : ℝ) ≤ p) (hMp : M ≤ Real.exp p) (hLp : L ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧
      ((N + 1 : ℕ) : ℝ) ≤ Real.exp (patchTopNetNumeratorLog s p + 2 * p + 6) ∧
      patchTopNetError d s N M < 1 / 4 ∧
      L * patchTopNetError d s N M ≤ Real.exp (-p) / 2 := by
  let b := patchTopNetNumeratorLog s p
  let E := b + 2 * p + 4
  let N := ⌈Real.exp E⌉₊
  have hb : 0 ≤ b := patchTopNetNumeratorLog_nonneg s hp
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hNlo : Real.exp E ≤ (N : ℝ) := Nat.le_ceil _
  have hNr : (0 : ℝ) < N := (Real.exp_pos E).trans_le hNlo
  have hN : 0 < N := by exact_mod_cast hNr
  have hNhi : ((N + 1 : ℕ) : ℝ) ≤ Real.exp (E + 2) := by
    have hc := (Nat.ceil_lt_add_one (Real.exp_nonneg E)).le
    have h1 := Real.one_le_exp hE
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    rw [Real.exp_add]
    push_cast
    have hmul := mul_le_mul_of_nonneg_left h3 (Real.exp_nonneg E)
    dsimp only [N] at *
    linarith
  have herr : patchTopNetError d s N M ≤ Real.exp (-2 * p - 4) := by
    rw [patchTopNetError_eq_div]
    apply (div_le_iff₀ hNr).mpr
    calc
      _ ≤ Real.exp b := patchTopNetNumerator_le_exp d s hp hM hd hMp
      _ = Real.exp (-2 * p - 4) * Real.exp E := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [E]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hNlo (Real.exp_nonneg _)
  have hfour : (4 : ℝ) < Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hsmall : Real.exp (-4 : ℝ) < 1 / 4 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hfour
  have hsmall' : patchTopNetError d s N M < 1 / 4 :=
    (herr.trans (Real.exp_le_exp.mpr (by linarith))).trans_lt hsmall
  have hloss : L * patchTopNetError d s N M ≤ Real.exp (-p) / 2 := by
    calc
      _ ≤ Real.exp p * Real.exp (-2 * p - 4) :=
        (mul_le_mul_of_nonneg_left herr hL).trans
          (mul_le_mul_of_nonneg_right hLp (Real.exp_nonneg _))
      _ = Real.exp (-p) * Real.exp (-4) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-p) * (1 / 2) :=
        mul_le_mul_of_nonneg_left (hsmall.le.trans (by norm_num)) (Real.exp_nonneg _)
      _ = _ := by ring
  have he : E + 2 = patchTopNetNumeratorLog s p + 2 * p + 6 := by dsimp only [E, b]; ring
  rw [he] at hNhi
  exact ⟨N, hN, hNhi, hsmall', hloss⟩

end Erdos3

end

end OAI
