import OAI.Combinatorics.Progressions.Dynamics.InitialConditioningBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem initial_conditioning_shell_sum_small {ι : Type*} (U : Finset ι)
    (n : ι → ℕ) (sourceRatio siteRatio error : ι → ℝ) (A B : ℕ)
    {V W countLog κ shell : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hn : ∀ i ∈ U, n i ≤ A)
    (hs0 : ∀ i ∈ U, 0 ≤ sourceRatio i) (ht0 : ∀ i ∈ U, 0 ≤ siteRatio i)
    (hs : ∀ i ∈ U, sourceRatio i ≤ Real.exp ((n i : ℝ) * V))
    (ht : ∀ i ∈ U, siteRatio i ≤ Real.exp ((n i : ℝ) * W))
    (herror : ∀ i ∈ U, |error i| ≤
      (2 : ℝ) ^ n i * (κ ^ (B - n i) * (sourceRatio i * 3) * (siteRatio i * 3)))
    (hcount : (U.card : ℝ) ≤ Real.exp countLog)
    (hκ0 : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hshell : 0 < shell)
    (hB : A + CyclicCrootSisask.spectralIterations shell
      ((A : ℝ) * (V + W + 1) + 4 + countLog) ≤ B) :
    (∑ i ∈ U, |error i|) ≤ shell / 16 := by
  let P := (A : ℝ) * (V + W + 1) + 4
  have hterm (i : ι) (hi : i ∈ U) : |error i| ≤ κ ^ (B - A) * Real.exp P := by
    have hpref := initial_conditioning_prefactor_le_exp (n i) (hs0 i hi) (ht0 i hi) (hs i hi) (ht i hi)
    have hn' : (n i : ℝ) ≤ A := by exact_mod_cast hn i hi
    have hp : Real.exp ((n i : ℝ) * (V + W + 1) + 4) ≤ Real.exp P := by
      apply Real.exp_le_exp.mpr
      dsimp only [P]
      gcongr
    have hpow : κ ^ (B - n i) ≤ κ ^ (B - A) :=
      pow_le_pow_of_le_one hκ0 (by linarith) (by have hni := hn i hi; omega)
    calc
      |error i| ≤ (2 : ℝ) ^ n i * (κ ^ (B - n i) * (sourceRatio i * 3) * (siteRatio i * 3)) := herror i hi
      _ = κ ^ (B - n i) * (9 * sourceRatio i * siteRatio i * (2 : ℝ) ^ n i) := by ring
      _ ≤ κ ^ (B - A) * Real.exp P :=
        mul_le_mul hpow (hpref.trans hp)
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hs0 i hi)) (ht0 i hi)) (by positivity))
          (pow_nonneg hκ0 _)
  have hsum : (∑ i ∈ U, |error i|) ≤ κ ^ (B - A) * ((U.card : ℝ) * Real.exp P) := by
    calc
      _ ≤ ∑ _i ∈ U, κ ^ (B - A) * Real.exp P := Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hpref : (U.card : ℝ) * Real.exp P ≤ Real.exp (P + countLog) := by
    calc
      _ ≤ Real.exp countLog * Real.exp P := mul_le_mul_of_nonneg_right hcount (Real.exp_pos P).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  apply hsum.trans
  apply geometric_tail_after_cutoff hshell hκ0 hκhalf (by positivity) hpref
  dsimp only [P]
  omega

end Erdos3

end

end OAI
