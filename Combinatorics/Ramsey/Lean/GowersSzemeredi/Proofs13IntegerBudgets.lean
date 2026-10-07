import GowersSzemeredi.Proofs13ExponentMargins
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Simultaneous integer budgets from strict power margins. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Filter

/-- Any strict power gap eventually absorbs a fixed multiplicative constant. -/
theorem eventually_nat_mul_rpow_le {a b C D : Real} (hab : a < b) (hD : 0 < D) :
    ∀ᶠ n : Nat in atTop, C * (n : Real) ^ a ≤ D * (n : Real) ^ b := by
  have ht : Tendsto (fun n : Nat => (n : Real) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (C / D)),
    eventually_ge_atTop (1 : Nat)] with n hn hnpos
  have hnreal : (0 : Real) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Real.rpow_sub hnreal] at hn
  have h := (div_le_div_iff₀ hD (Real.rpow_pos_of_pos hnreal a)).mp hn
  simpa only [mul_comm D] using h

/-- Choose the ceiling of a prescribed power-law target. Strict exponent
margins give all the integer, recurrence, Bohr-radius, and width budgets at
once, uniformly over progression lengths P and Q satisfying the two lower
bounds. No explicit value for the sufficiently-large threshold is asserted. -/
theorem eventually_rounded_power_budgets
    {c d z W e u v w f : Real}
    (hc : 0 < c) (hd : 0 < d) (hz : 0 < z)
    (he : 0 < e) (hv : 0 < v) (hw : 0 < w) (hf : 0 < f)
    (hsquare : 2 * e < 1) (hrec : e < u * v) (hbohr : e < u * w) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ P Q : Real,
      d * (N : Real) ^ u ≤ P → P ^ v / 2 ≤ Q →
      ∃ m : Nat, 0 < m ∧ m ^ 2 ≤ N ∧ (m : Real) + 1 ≤ Q ∧
        c * (N : Real) ^ e ≤ m ∧ P ^ (-w) ≤ z / m ∧
        W ≤ (c * (N : Real) ^ e) ^ f := by
  have ht := eventually_nat_mul_rpow_le (C := 1) (D := c) he hc
  have hs := eventually_nat_mul_rpow_le (C := 4 * c ^ 2) (D := 1) hsquare zero_lt_one
  have hr := eventually_nat_mul_rpow_le (C := 3 * c) (D := d ^ v / 2) hrec
    (div_pos (Real.rpow_pos_of_pos hd _) (by norm_num))
  have hb := eventually_nat_mul_rpow_le (C := 2 * c) (D := z * d ^ w) hbohr
    (mul_pos hz (Real.rpow_pos_of_pos hd _))
  have hwidth := eventually_nat_mul_rpow_le (C := W) (D := c ^ f)
    (mul_pos he hf) (Real.rpow_pos_of_pos hc _)
  have hall : ∀ᶠ N : Nat in atTop, ∀ P Q : Real,
      d * (N : Real) ^ u ≤ P → P ^ v / 2 ≤ Q →
      ∃ m : Nat, 0 < m ∧ m ^ 2 ≤ N ∧ (m : Real) + 1 ≤ Q ∧
        c * (N : Real) ^ e ≤ m ∧ P ^ (-w) ≤ z / m ∧
        W ≤ (c * (N : Real) ^ e) ^ f := by
    filter_upwards [ht, hs, hr, hb, hwidth, eventually_ge_atTop (1 : Nat)] with
      N ht hs hr hb hwidth hN
    intro P Q hP hQ
    have hNpos : (0 : Real) < N := by exact_mod_cast (by omega : 0 < N)
    let t : Real := c * (N : Real) ^ e
    let m : Nat := Nat.ceil t
    have htpos : 0 < t := mul_pos hc (Real.rpow_pos_of_pos hNpos e)
    have htone : 1 ≤ t := by simpa only [Real.rpow_zero, mul_one] using ht
    have hmpos : 0 < m := Nat.one_le_ceil_iff.mpr htpos
    have hmlower : t ≤ (m : Real) := Nat.le_ceil t
    have hmround : (m : Real) < t + 1 := Nat.ceil_lt_add_one htpos.le
    have hmupper : (m : Real) ≤ 2 * t := by linarith only [hmround, htone]
    have hmadd : (m : Real) + 1 ≤ 3 * t := by linarith only [hmround, htone]
    have hPpos : 0 < P := (mul_pos hd (Real.rpow_pos_of_pos hNpos u)).trans_le hP
    have hpow (s : Real) : (d * (N : Real) ^ u) ^ s = d ^ s * (N : Real) ^ (u * s) := by
      rw [Real.mul_rpow hd.le (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le]
    have hmsquare : (m : Real) ^ 2 ≤ (N : Real) := by
      calc
        _ ≤ (2 * t) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmupper 2
        _ = 4 * c ^ 2 * (N : Real) ^ (2 * e) := by
          dsimp [t]
          rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hNpos.le]
          ring_nf
        _ ≤ _ := by simpa only [Real.rpow_one, one_mul] using hs
    refine ⟨m, hmpos, ?_, ?_, hmlower, ?_, ?_⟩
    · exact_mod_cast hmsquare
    · calc
        _ ≤ 3 * t := hmadd
        _ ≤ (d * (N : Real) ^ u) ^ v / 2 := by rw [hpow]; dsimp [t]; nlinarith only [hr]
        _ ≤ P ^ v / 2 := div_le_div_of_nonneg_right (Real.rpow_le_rpow
          (mul_pos hd (Real.rpow_pos_of_pos hNpos u)).le hP hv.le) (by norm_num)
        _ ≤ Q := hQ
    · have hmP : (m : Real) ≤ z * P ^ w := by
        calc
          _ ≤ 2 * t := hmupper
          _ ≤ z * (d * (N : Real) ^ u) ^ w := by rw [hpow]; dsimp [t]; nlinarith only [hb]
          _ ≤ z * P ^ w := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (mul_pos hd (Real.rpow_pos_of_pos hNpos u)).le hP hw.le) hz.le
      rw [Real.rpow_neg hPpos.le, ← one_div]
      apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hPpos _) (by exact_mod_cast hmpos)).mpr
      simpa only [one_mul] using hmP
    · rw [Real.mul_rpow hc.le (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le]
      simpa only [Real.rpow_zero, mul_one] using hwidth
  exact eventually_atTop.mp hall

end LeanProofs.GowersSzemeredi
