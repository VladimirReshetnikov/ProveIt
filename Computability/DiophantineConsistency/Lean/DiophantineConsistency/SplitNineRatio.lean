import DiophantineConsistency.NativeBaseBounds52
import DiophantineConsistency.MaskPopulation
import DiophantineConsistency.FreeCarrierRatio

/-! # Numerical outer registers for the split116 equation

The two source words remain supplied natural data. This module connects
their reduced rank and actual sparse mask to the checked ratio/finalizer,
without assuming a source compiler or a source zero.
-/

namespace DiophantineConsistency.SplitNineRatio

open Jones1982 FreeCarrierRatio

def base (a b : ℕ) : ℕ := NativeBaseBounds52.base (2 ^ a) b
def blockLength (a b : ℕ) : ℕ := b * (base a b) ^ 2279
def threshold (a b : ℕ) : ℕ := 2 ^ (8 * a + 85) * b * (base a b) ^ 1201
def rank (a b S T : ℕ) : ℕ := ReducedRankCarry.rank (blockLength a b) S T
def marginScale (a b : ℕ) : ℕ := b * (base a b) ^ 116
def cap (a b : ℕ) : ℕ := 32 * marginScale a b

def value (a b g S T : ℕ) (v : FreeVars) (n : ℕ) : ℤ :=
  v.finalValue (rank a b S T) (threshold a b) b g (cap a b) (marginScale a b) n

theorem base_bounds (a : ℕ) {b : ℕ} (hb : 0 < b) :
    4096 ≤ base a b ∧ 4 * b < base a b := by
  have hH : 1 ≤ (2 : ℕ) ^ a := Nat.one_le_two_pow
  have hb2 : 1 ≤ b ^ 2 := by have h := pow_pos hb 2; omega
  have hprod : 1 ≤ 2 ^ a * b ^ 2 := by simpa using Nat.mul_le_mul hH hb2
  have hlarge : 4096 ≤ base a b := by
    unfold base NativeBaseBounds52.base
    nlinarith only [hprod]
  exact ⟨hlarge, NativeBaseBounds52.base_gt_four_digits (by positivity) hb⟩

theorem size_bounds (a S T : ℕ) {b : ℕ} (hb : 0 < b) :
    8 ≤ rank a b S T ∧ 8 ≤ threshold a b ∧ b ≤ rank a b S T ∧
      b ≤ threshold a b ∧ 0 < cap a b := by
  obtain ⟨hB, hbB⟩ := base_bounds a hb
  have hBp : base a b ≤ (base a b) ^ 2279 := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ (by omega : 1 ≤ base a b) (by decide : 1 ≤ 2279))
  have hL : b + 8 ≤ blockLength a b := by
    unfold blockLength
    have h := Nat.mul_le_mul_left b hBp
    nlinarith only [h, hB, hbB, hb]
  have hR := ReducedRankCarry.rank_ge (L := blockLength a b) (S := S) (T := T)
  have hc : 8 ≤ (2 : ℕ) ^ (8 * a + 85) := by
    calc 8 = (2 : ℕ) ^ 3 := by decide
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hp : 1 ≤ (base a b) ^ 1201 := by
    have h := pow_pos (by omega : 0 < base a b) 1201
    omega
  have hN : 8 * b ≤ threshold a b := by
    unfold threshold
    nlinarith only [Nat.mul_le_mul_right b hc,
      Nat.mul_le_mul_left (2 ^ (8 * a + 85) * b) hp]
  have hcap : 0 < cap a b := by unfold cap marginScale; positivity
  exact ⟨by change 8 ≤ ReducedRankCarry.rank _ _ _; omega,
    by omega, by change b ≤ ReducedRankCarry.rank _ _ _; omega, by omega, hcap⟩

theorem base_power {a b k : ℕ} (hb : b = 2 ^ k) :
    base a b = 2 ^ (a + 12 + 2 * k) := by
  rw [base, hb, NativeBaseBounds52.base_power]

theorem blockLength_power {a b k : ℕ} (hb : b = 2 ^ k) :
    blockLength a b = 2 ^ (k + 2279 * (a + 12 + 2 * k)) := by
  rw [blockLength, base_power hb, hb, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem threshold_power {a b k : ℕ} (hb : b = 2 ^ k) :
    threshold a b = 2 ^ ((8 * (a + 12) - 11) + k + 1201 * (a + 12 + 2 * k)) := by
  rw [threshold, base_power hb, hb, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  omega

theorem rank_cast (a S T : ℕ) {b : ℕ} (hb : 0 < b) :
    (rank a b S T : ℤ) = (blockLength a b : ℤ) * ((S : ℤ) + T + 1) - S - 1 := by
  apply ReducedRankCarry.rank_cast
  unfold blockLength
  have hB := (base_bounds a hb).1
  have h : 0 < b * (base a b) ^ 2279 := by positivity
  omega

/-- The literal masks determine the exact threshold, rather than supplying
a population equation as a premise. The low code alone needs a range bound. -/
theorem binomial_iff {a b k S highLen : ℕ} (hb : b = 2 ^ k)
    (low high : Finset ℕ) (hlow : low ⊆ Finset.range 117)
    (hhigh : high ⊆ Finset.range highLen) (h31 : low.card = 31) (h22 : high.card = 22)
    (hS : S < blockLength a b) :
    let T := MaskPopulation.packedMask (base a b) b 117 low high
    (threshold a b) ^ 2 ∣ (2 * rank a b S T).choose (rank a b S T) ↔ τ 2 S T = 0 := by
  have hrange := hS
  rw [blockLength_power hb] at hrange
  dsimp only
  unfold rank
  rw [base_power hb, blockLength_power hb, threshold_power hb, hb]
  exact MaskPopulation.split116_binomial_iff (kappa := a + 12) (by omega)
    low high hlow hhigh h31 h22 hrange

/-- A final equation zero first recovers the power-of-two base and weak cap.
No source word bounds or source-zero assumptions are needed here. -/
theorem sound (a b g S T : ℕ) (v : FreeVars) (hb : 0 < b)
    (hh : 0 < v.h) (hs : 0 < v.s) (hw : 0 < v.w) (hC : 0 < v.C) (hi : 0 < v.i)
    (hz : ∃ n : ℕ, 0 < n ∧ value a b g S T v n = 0) :
    (threshold a b) ^ 2 ∣ (2 * rank a b S T).choose (rank a b S T) ∧
      (∃ k, b = 2 ^ k) ∧ g < 4 * b * (base a b) ^ 116 := by
  obtain ⟨hR, hN, hbR, hbN, hcap⟩ := size_bounds a S T hb
  obtain ⟨hdvd, hpow, hg⟩ := ratio_sound v hR hN hbR hb hbN hcap rfl hh hs hw hC hi hz
  refine ⟨hdvd, hpow, ?_⟩
  unfold cap marginScale at hg
  nlinarith only [hg]

/-- The stronger source-code cap gives the converse, with every required
coordinate and the final witness strictly positive. -/
theorem complete (a b g S T : ℕ) (hb : 0 < b)
    (hcap : g < b * (base a b) ^ 116)
    (hdvd : (threshold a b) ^ 2 ∣ (2 * rank a b S T).choose (rank a b S T))
    (hpow : ∃ k, b = 2 ^ k) :
    ∃ v : FreeVars, 0 < v.h ∧ 0 < v.s ∧ 0 < v.w ∧ 0 < v.C ∧ 0 < v.i ∧
      ∃ n : ℕ, 0 < n ∧ value a b g S T v n = 0 := by
  obtain ⟨hR, hN, hbR, hbN, _⟩ := size_bounds a S T hb
  have hg : 32 * g < cap a b := by unfold cap marginScale; nlinarith only [hcap]
  exact ratio_complete hR hN hbR hb hbN rfl hg hdvd hpow

end DiophantineConsistency.SplitNineRatio
