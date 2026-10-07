import OAI.Combinatorics.Progressions.Dynamics.ModeThresholdLogBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def modeRankLog (m : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) + 1 + ∑ i : Fin m,
    ((((i.val + 1).factorial : ℝ) + P + (i.val + 1 : ℕ) * P) +
      P ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P) +
      ((i.val + 1 : ℕ) * P + (i.val + 1 : ℕ) * (modeShrinkLog m P + 2) + modeBiasLog m P) + 2)

theorem modeRankLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) : 0 ≤ modeRankLog m P := by
  have hb := modeBiasLog_nonneg m hP
  have ht := modeShrinkLog_nonneg m hP
  unfold modeRankLog
  positivity

theorem modeRemovalRankThreshold_le_exp (m n d : ℕ) {P C D S ρ ε : ℝ}
    (hP : 0 ≤ P) (hn : (n : ℝ) ≤ P) (hd : (d : ℝ) ≤ P)
    (hC : 0 ≤ C) (hCP : C ≤ Real.exp P) (hD : 0 ≤ D) (hDP : D ≤ Real.exp P)
    (hS : 0 ≤ S) (hSP : S ≤ Real.exp P) (hρ : 0 < ρ) (hρInv : 1 / ρ ≤ Real.exp P)
    (hε : 0 < ε) (hεInv : 1 / ε ≤ Real.exp P) :
    modeRemovalRankThreshold m n d C D S ρ ε ≤ Real.exp (modeRankLog m P) := by
  let B := finiteLayerBiasBudget m (modeRemovalBias m ε)
  let A := 2 * modeRemovalShrink m d D ρ ε
  have hB : B ≤ Real.exp (modeBiasLog m P) := chosenBiasBudget_le_exp m hP hε hεInv
  have hB0 : 0 ≤ B := zero_le_one.trans (finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε))
  have hT0 := modeRemovalShrink_one_le m d hD hρ hε
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hT := modeRemovalShrink_le_exp m d hP hd hD hDP hρ hρInv hε hεInv
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hA : A ≤ Real.exp (modeShrinkLog m P + 2) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (modeShrinkLog m P) := by dsimp [A]; gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hnp : (n : ℝ) ≤ Real.exp P := hn.trans (by linarith [Real.add_one_le_exp P])
  have hBL := modeBiasLog_nonneg m hP
  have hTL := modeShrinkLog_nonneg m hP
  let cost (i : Fin m) := ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) +
    (B * S ^ (i.val + 1)) ^ (n ^ (i.val + 1)) +
    (n : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B)
  let bound (i : Fin m) :=
    ((((i.val + 1).factorial : ℝ) + P + (i.val + 1 : ℕ) * P) +
      P ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P) +
      ((i.val + 1 : ℕ) * P + (i.val + 1 : ℕ) * (modeShrinkLog m P + 2) + modeBiasLog m P) + 2)
  have hbound i : 0 ≤ bound i := by dsimp [bound]; positivity
  have hcost (i : Fin m) : cost i ≤ Real.exp (bound i) := by
    have hf : ((i.val + 1).factorial : ℝ) ≤ Real.exp ((i.val + 1).factorial : ℝ) := by
      linarith [Real.add_one_le_exp ((i.val + 1).factorial : ℝ)]
    have hrow : ((i.val + 1).factorial : ℝ) * (C * D ^ (i.val + 1)) ≤
        Real.exp (((i.val + 1).factorial : ℝ) + P + (i.val + 1 : ℕ) * P) := by
      calc
        _ ≤ Real.exp ((i.val + 1).factorial : ℝ) * (Real.exp P * (Real.exp P) ^ (i.val + 1)) := by gcongr
        _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hden : (B * S ^ (i.val + 1)) ^ (n ^ (i.val + 1)) ≤
        Real.exp (P ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P)) := by
      calc
        _ ≤ (Real.exp (modeBiasLog m P) * (Real.exp P) ^ (i.val + 1)) ^ (n ^ (i.val + 1)) := by gcongr
        _ = Real.exp ((n : ℝ) ^ (i.val + 1) * (modeBiasLog m P + (i.val + 1 : ℕ) * P)) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul, Nat.cast_pow]
        _ ≤ _ := Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hn _) (by positivity))
    have hcoeff : (n : ℝ) ^ (i.val + 1) * (A ^ (i.val + 1) * B) ≤
        Real.exp ((i.val + 1 : ℕ) * P + (i.val + 1 : ℕ) * (modeShrinkLog m P + 2) + modeBiasLog m P) := by
      calc
        _ ≤ (Real.exp P) ^ (i.val + 1) * ((Real.exp (modeShrinkLog m P + 2)) ^ (i.val + 1) *
          Real.exp (modeBiasLog m P)) := by gcongr
        _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsum := add_le_exp_add_one (by positivity) (by positivity) hrow hden
    have hsum' := add_le_exp_add_one (by positivity) (by positivity) hsum hcoeff
    convert hsum' using 1
    congr 1
    dsimp [bound]
    ring
  have hsum := sum_le_exp_card_add_sum cost bound hbound hcost
  have hout := one_add_le_exp_succ (by positivity) hsum
  change 1 + ∑ i : Fin m, cost i ≤ _
  convert hout using 1
  congr 1
  simp only [modeRankLog, Fintype.card_fin]
  dsimp [bound]
  ring

end Erdos3

end

end OAI
