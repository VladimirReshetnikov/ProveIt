import DiophantineConsistency.P138.P138FirstIndex
import DiophantineConsistency.ArithmeticHalfBinomialSandwich
import DiophantineConsistency.Compact44.P72ConvArith

/-! # The ratio bound `|H| > x (x − 3)^t`

132-lowops §5 ("the retained sign-uniform ratio bound"). At a zero, write `R = 2t + 1`
(`P138Rank`), so the first index is `n = t + 1` (`P138FirstIndex`), and put `x = |X|`. Then

* `|c| = ψ_b(2t+1) ≥ (2B − 1)^(2t)` with `B = |A|` (`power_le_ycoord`);
* `|k|/2 = ψ_bF(t+1) ≤ (2P)^t` with `P = bF + 2 ≤ 2x|Y|² + 1` (`ycoord_le_power`);
* `(2B − 1)² ≥ (x − 3)·2P` (elementary, `|Y| ≥ 6`);
* `2|c| < |k|(2|Y| + 1)` (`P138Budget.c_interval`), so `(x − 3)^t < 2|Y| + 1`;
* `|H| = |4a + 3| ≥ 4|Y|(x − 1) − 3 ≥ x(2|Y| + 1)`.

Hence `x (x − 3)^t < |H|` (`H_large`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138Ratio
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap P138NoRoot
  P138Squares P138Budget P138Adjacent P138Window P138EarlyFold P138Rank P138FirstIndex
open ArithmeticPellRecurrence ArithmeticPow ArithmeticHalfBinomialSandwich

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem power_double (z t : V) : power z (2 * t) = power (z * z) t := by
  rw [power_mul_base, ← power_add, two_mul]

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ : DiffRing V)
local notation "𝓡" => regsK p x κ

theorem abs_X_ge (hp : PortFacts p) : 2 ^ 66 ≤ |(𝓡).X| := by
  have := abs_X p x κ hp; have := abs_q_ge p x κ hp
  have e : (2 : DiffRing V) ^ 66 = 4 * 2 ^ 64 := by norm_num
  linarith

theorem six_le_abs_Y (hp : PortFacts p) : 6 ≤ |(𝓡).Y| := by
  have hq := abs_q_ge p x κ hp
  have h64 : (6 : DiffRing V) ≤ 2 ^ 64 := by norm_num
  have hq3 : |(𝓡).q| ≤ |(𝓡).q| ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
  linarith [abs_Y p x κ hp]

/-- `|A| ≥ |Y| (|X| − 1) − 2`. -/
theorem abs_A_ge : |(𝓡).Y| * (|(𝓡).X| - 1) - 2 ≤ |(𝓡).A| := by
  have e : (𝓡).A = (𝓡).Y * ((𝓡).X + 1) + 2 := by rw [A_eq, a_eq]; ring
  have h1 : |(𝓡).Y| * (|(𝓡).X| - 1) ≤ |(𝓡).Y * ((𝓡).X + 1)| := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := abs_sub_abs_le_abs_sub (𝓡).X (-1)
    rw [abs_neg, abs_one, sub_neg_eq_add] at this; exact this
  have h2 : |(𝓡).Y * ((𝓡).X + 1)| - 2 ≤ |(𝓡).A| := by
    rw [e]
    have := abs_sub_abs_le_abs_sub ((𝓡).Y * ((𝓡).X + 1)) (-2)
    rw [abs_neg, abs_two, sub_neg_eq_add] at this; exact this
  linarith

/-- `|H| ≥ |X| (2|Y| + 1)`. -/
theorem abs_H_ge (hp : PortFacts p) : |(𝓡).X| * (2 * |(𝓡).Y| + 1) ≤ |(𝓡).H| := by
  have hX := abs_X_ge p x κ hp
  have hY := six_le_abs_Y p x κ hp
  have h66 : (8 : DiffRing V) ≤ 2 ^ 66 := by norm_num
  have ha : |(𝓡).Y| * (|(𝓡).X| - 1) ≤ |(𝓡).a| := by
    rw [a_eq, show (𝓡).X * (𝓡).Y + (𝓡).Y = (𝓡).Y * ((𝓡).X + 1) by ring, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have := abs_sub_abs_le_abs_sub (𝓡).X (-1)
    rw [abs_neg, abs_one, sub_neg_eq_add] at this; exact this
  have hH : 4 * |(𝓡).a| - 3 ≤ |(𝓡).H| := by
    rw [H_def]
    have := abs_sub_abs_le_abs_sub (4 * (𝓡).a) (-3)
    rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : DiffRing V) ≤ 4),
      abs_of_nonneg (by norm_num : (0 : DiffRing V) ≤ 3), sub_neg_eq_add] at this
    exact this
  have hX8 : 8 ≤ |(𝓡).X| := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hX8) (sub_nonneg.mpr hY)
  nlinarith

/-- `(2B − 1)² ≥ (x − 3)·2P` with `B = |A|`, `P ≤ 2x|Y|² + 1`. -/
theorem base_square (hp : PortFacts p) {P : DiffRing V}
    (hP : P ≤ 2 * |(𝓡).X| * |(𝓡).Y| ^ 2 + 1) :
    (|(𝓡).X| - 3) * (2 * P) ≤ (2 * |(𝓡).A| - 1) * (2 * |(𝓡).A| - 1) := by
  have hX := abs_X_ge p x κ hp
  have hY := six_le_abs_Y p x κ hp
  have h66 : (8 : DiffRing V) ≤ 2 ^ 66 := by norm_num
  have hA := abs_A_ge p x κ
  set xx := |(𝓡).X|
  set yy := |(𝓡).Y|
  have hX8 : 8 ≤ xx := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hX8) (sub_nonneg.mpr hY)
  have hL : 0 ≤ 2 * yy * (xx - 1) - 5 := by nlinarith
  have h1 : (2 * yy * (xx - 1) - 5) * (2 * yy * (xx - 1) - 5) ≤
      (2 * |(𝓡).A| - 1) * (2 * |(𝓡).A| - 1) :=
    mul_le_mul (by linarith) (by linarith) hL (by linarith)
  have h2 : (xx - 3) * (2 * P) ≤ (xx - 3) * (4 * xx * yy ^ 2 + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : (xx - 3) * (4 * xx * yy ^ 2 + 2) ≤ (2 * yy * (xx - 1) - 5) * (2 * yy * (xx - 1) - 5) := by
    have : 0 ≤ xx * (4 * yy ^ 2 - 20 * yy - 2) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  linarith

/-- **The ratio bound.** -/
theorem H_large (hp : PortFacts p) (Fd : Folded p x κ) (Fi : FirstIndex p x κ Fd) (t xn : V)
    (ht : Fd.Rn = 2 * t + 1)
    (hxn : |(𝓡).X| = ι xn) :
    (ι (xn * power (xn - 3) t) : DiffRing V) < |(𝓡).H| := by
  have hB : 0 < (𝓡).Budget := Fd.hbudget
  have hci := (c_interval p x κ hp hB).2.1
  obtain ⟨yn, hyn⟩ := abs_eq_ι (𝓡).Y
  have hX := abs_X_ge p x κ hp
  have hY := six_le_abs_Y p x κ hp
  have hn : Fi.n = t + 1 := by
    have h := Fi.hn; rw [ht] at h
    apply ι_injective
    have h' := congrArg (ι (V := V)) h
    simp only [map_add, map_mul, map_ofNat, map_one] at h' ⊢
    linarith
  -- `x − 3` as a natural number
  have hx3 : (3 : V) ≤ xn := by
    apply ι_le_ι.mp; rw [map_ofNat, ← hxn]
    have : (3 : DiffRing V) ≤ 2 ^ 66 := by norm_num
    linarith
  have hxsub : (ι (xn - 3) : DiffRing V) = |(𝓡).X| - 3 := by rw [ι_tsub' hx3, map_ofNat, hxn]
  -- the two Pell growth bounds
  set b := Fd.Bn - 2 with hb
  have hb2 : (ι (2 * b + 3) : DiffRing V) = 2 * |(𝓡).A| - 1 := by
    rw [hb]; simp only [map_add, map_mul, map_ofNat]
    rw [ι_tsub' (le_trans (by norm_num) Fd.hB3), map_ofNat, ← Fd.hBn]; ring
  have hc1 : power ((2 * b + 3) * (2 * b + 3)) t ≤ Fd.cn := by
    rw [← power_double, Fd.hc, ht]
    exact power_le_ycoord b (2 * t)
  have hK1 : ycoord (t + 1) Fi.bF ≤ power (2 * (Fi.bF + 2)) t := ycoord_le_power Fi.bF t
  -- the base comparison
  have hbase : (xn - 3) * (2 * (Fi.bF + 2)) ≤ (2 * b + 3) * (2 * b + 3) := by
    apply ι_le_ι.mp
    simp only [map_mul, map_ofNat]
    rw [hxsub, hb2, map_add, map_ofNat]
    exact base_square p x κ hp Fi.hbFhi
  have hPpos : 0 < power (2 * (Fi.bF + 2)) t := power_pos _ _ (by simp)
  have hprod : power (xn - 3) t * power (2 * (Fi.bF + 2)) t ≤ Fd.cn := by
    rw [← power_mul_base]
    exact le_trans (power_mono_base _ _ t hbase) hc1
  -- `2|c| < |k|(2|Y| + 1)` with `|k| = 2ψ_bF(t+1)`
  have hck : Fd.cn < ycoord (t + 1) Fi.bF * (2 * yn + 1) := by
    apply ι_lt_ι.mp
    rw [Fd.hcn, Fi.hk, hn, hyn] at hci
    simp only [map_mul, map_add, map_ofNat, map_one] at hci ⊢
    linarith
  have hlt : power (xn - 3) t * power (2 * (Fi.bF + 2)) t <
      power (2 * (Fi.bF + 2)) t * (2 * yn + 1) := by
    calc power (xn - 3) t * power (2 * (Fi.bF + 2)) t ≤ Fd.cn := hprod
      _ < ycoord (t + 1) Fi.bF * (2 * yn + 1) := hck
      _ ≤ power (2 * (Fi.bF + 2)) t * (2 * yn + 1) := mul_le_mul_of_nonneg_right hK1 (by simp)
  have hpow : power (xn - 3) t < 2 * yn + 1 := by
    rw [mul_comm (power (2 * (Fi.bF + 2)) t)] at hlt
    exact lt_of_mul_lt_mul_right hlt (by simp)
  have hH := abs_H_ge p x κ hp
  rw [hxn, hyn] at hH
  have hxpos : (0 : DiffRing V) < ι xn := by rw [← hxn]; linarith
  have : (ι (xn * power (xn - 3) t) : DiffRing V) < ι xn * (2 * ι yn + 1) := by
    rw [map_mul]
    apply mul_lt_mul_of_pos_left _ hxpos
    have := ι_lt_ι.mpr hpow
    simpa only [map_add, map_mul, map_ofNat, map_one] using this
  linarith

end Regs

#print axioms abs_H_ge
#print axioms base_square
#print axioms H_large

end DiophantineConsistency.P138Ratio
