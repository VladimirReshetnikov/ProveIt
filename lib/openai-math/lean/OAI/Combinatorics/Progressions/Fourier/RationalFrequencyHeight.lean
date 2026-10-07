import OAI.Combinatorics.Progressions.Estimates.NativeCentralSeed

namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {L ι κ : Type*} [AddCommGroup L] [Module ℚ L]

theorem basisFrequency_logHeight_le (e : Basis κ ℚ L) (b : Basis ι ℚ L)
    (S : Set ι) [Fintype S] (N : ℕ) (hN : 0 < N) (n : S → ℤ)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card S : ℝ) ≤ p)
    (hNp : (N : ℝ) ≤ Real.exp p) (hn : ∀ j, (|n j| : ℝ) ≤ Real.exp p)
    (hb : ∀ i j, rationalLogHeight (b.repr (e i) j) ≤ p) (i : κ) :
    rationalLogHeight (basisFrequency b S N n (e i)) ≤ (p + 2) ^ 4 := by
  classical
  let H := ⌈Real.exp p⌉₊
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hfrac (j : S) : RationalHeightLE ((n j : ℚ) / (N : ℚ)) H := by
    have ha : (n j).natAbs ≤ H := by
      apply (Nat.cast_le (α := ℝ)).mp
      simpa only [Nat.cast_natAbs, Int.cast_abs] using (hn j).trans (Nat.le_ceil (Real.exp p))
    have hbN : (N : ℤ).natAbs ≤ H := by
      simpa only [Int.natAbs_natCast] using
        (Nat.cast_le.mp (hNp.trans (Nat.le_ceil (Real.exp p))) : N ≤ H)
    simpa only [Int.cast_natCast] using
      rationalHeightLE_fraction (n j) (N : ℤ) (by exact_mod_cast hN.ne') ha hbN
  have hterms (j : S) :
      RationalHeightLE (((n j : ℚ) / (N : ℚ)) * b.repr (e i) j) (H * H) :=
    (hfrac j).mul (rationalHeightLE_ceil_exp (hb i j))
  have hHH : ((H * H : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp (p + 1) * Real.exp (p + 1) := by gcongr
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg p])
  rw [basisFrequency_apply]
  apply (rationalLogHeight_le_iff _ _).mpr
  simpa only [show (2 + 1 + 1 : ℕ) = 4 from rfl] using
    rational_sum_exp_height _ hterms hp 2 1 hHH (by simpa using hd.trans (by linarith : p ≤ p + 2))

end Erdos3

end

end OAI
