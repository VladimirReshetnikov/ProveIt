import Diophantine.Paper1976.MR

/-!
# The merged growth square after Theorem 3.9

Condition (24) replaces the first two square tests for the construction.
Its coprime factors force the required lower bounds on `n` and `x`; it
does not assert that the old second radicand `U(2n,x)` is a square.
For each admissible `n`, Pell solutions supply arbitrarily large `x`.
-/

namespace JSWW1976

open Diophantine Pell

/-- The second factor of (24), with its nonnegative expanded coefficient. -/
def fiveSquareSecond (k n x : ℕ) : ℕ :=
  let T := U (2 * k) n
  16 * T * (T - 1) * (n + 1) ^ 2 * (x + 1) ^ 2 + 1

/-- The single square radicand replacing (I) and (II) for the construction. -/
def fiveSquareRadicand (k n x : ℕ) : ℕ :=
  U (2 * k) n * fiveSquareSecond k n x

private theorem fiveSquare_U_lower (k n : ℕ) : n + 2 ≤ U (2 * k) n := by
  have hc : 0 < (2 * k + 2) ^ 3 * (2 * k + 4) := by positivity
  have h1 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have h2 : (n + 1) ^ 2 ≤ (2 * k + 2) ^ 3 * (2 * k + 4) * (n + 1) ^ 2 :=
    Nat.le_mul_of_pos_left _ hc
  unfold U
  omega

/-- The expanded second factor is exactly a Pell square condition. -/
theorem fiveSquareSecond_eq_pell (k n x : ℕ) :
    fiveSquareSecond k n x =
      ((2 * U (2 * k) n - 1) * (2 * U (2 * k) n - 1) - 1) *
        (2 * (n + 1) * (x + 1)) ^ 2 + 1 := by
  let T := U (2 * k) n
  have hT : 1 ≤ T := by have := fiveSquare_U_lower k n; dsimp [T]; omega
  have h2T : 1 ≤ 2 * T := by omega
  have ha : 1 ≤ 2 * T - 1 := by omega
  have haa : 1 ≤ (2 * T - 1) * (2 * T - 1) := Nat.mul_le_mul ha ha
  change 16 * T * (T - 1) * (n + 1) ^ 2 * (x + 1) ^ 2 + 1 =
    ((2 * T - 1) * (2 * T - 1) - 1) * (2 * (n + 1) * (x + 1)) ^ 2 + 1
  zify [hT, h2T, haa]
  ring

/-- Agreement with the literal unexpanded formula (24). -/
theorem fiveSquareRadicand_eq_original (k n x : ℕ) :
    fiveSquareRadicand k n x = U (2 * k) n *
      (((2 * U (2 * k) n - 1) ^ 2 - 1) * (n + 1) ^ 2 * (x + 1) ^ 2 * 4 + 1) := by
  rw [fiveSquareRadicand, fiveSquareSecond_eq_pell]
  rw [← pow_two (2 * U (2 * k) n - 1)]
  ring

/-- The second factor is one modulo the first, so their gcd is one. -/
theorem fiveSquare_factors_coprime (k n x : ℕ) :
    Nat.Coprime (U (2 * k) n) (fiveSquareSecond k n x) := by
  have hmod : fiveSquareSecond k n x ≡ 1 [MOD U (2 * k) n] := by
    change (16 * U (2 * k) n * (U (2 * k) n - 1) * (n + 1) ^ 2 * (x + 1) ^ 2 + 1) %
      U (2 * k) n = 1 % U (2 * k) n
    simp [Nat.add_mod, Nat.mul_mod]
  have h := hmod.gcd_eq
  simp only [Nat.gcd_one_left] at h
  exact Nat.Coprime.symm h

/-- The merged square separates into precisely its two coprime square factors. -/
theorem fiveSquareRadicand_isSquare_iff (k n x : ℕ) :
    IsSquare (fiveSquareRadicand k n x) ↔
      IsSquare (U (2 * k) n) ∧ IsSquare (fiveSquareSecond k n x) := by
  rw [fiveSquareRadicand]
  have hc := fiveSquare_factors_coprime k n x
  constructor
  · intro h
    exact ⟨IsSquare.of_coprime_mul hc h,
      IsSquare.of_coprime_mul hc.symm (by simpa only [mul_comm] using h)⟩
  · rintro ⟨hT, hsecond⟩
    exact hT.mul hsecond

/-- Condition (24) supplies the two growth hypotheses used by Theorem 3.9. -/
theorem fiveSquareRadicand_growth {k n x : ℕ} (hk : 1 ≤ k)
    (h : IsSquare (fiveSquareRadicand k n x)) :
    IsSquare (U (2 * k) n) ∧ (2 * k) ^ (2 * k) < n ∧ (2 * n) ^ (2 * n) < x := by
  obtain ⟨hT_square, hsecond⟩ := (fiveSquareRadicand_isSquare_iff k n x).mp h
  have hn : (2 * k) ^ (2 * k) < n := lt_of_U_square hT_square
  have hkn : k < n := by
    have hpow : 2 * k ≤ (2 * k) ^ (2 * k) := Nat.le_self_pow (by omega) _
    omega
  have hnpos : 0 < n := by omega
  let T := U (2 * k) n
  let a := 2 * T - 1
  let d := 2 * (n + 1)
  have hT : n + 2 ≤ T := fiveSquare_U_lower k n
  have ha : 1 < a := by dsimp [a]; omega
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hda : d ∣ a - 1 := by
    have he : a - 1 = 2 * (T - 1) := by dsimp [a]; omega
    rw [he]
    refine ⟨(2 * k + 2) ^ 3 * (2 * k + 4) * (n + 1), ?_⟩
    simp only [T, U, d, Nat.add_sub_cancel]
    ring
  rw [fiveSquareSecond_eq_pell] at hsecond
  change IsSquare ((a * a - 1) * (d * (x + 1)) ^ 2 + 1) at hsecond
  obtain ⟨j, hj⟩ := exists_eq_ψ_of_square ha hsecond
  have hmod : ψ ha j ≡ j [MOD d] := Nat.ModEq.of_dvd hda (ψ_modEq ha j)
  have hdy : d ∣ ψ ha j := ⟨x + 1, hj.symm⟩
  have hdj : d ∣ j :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdy))
  have hjpos : 0 < j := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hypos : 0 < d * (x + 1) := by positivity
    simp only [hzero, ψ, yn_zero] at hj
    omega
  have hdle : d ≤ j := Nat.le_of_dvd hjpos hdj
  have hexp : 2 * n + 1 ≤ j - 1 := by dsimp [d] at hdle; omega
  have hpower : (2 * a - 1) ^ (2 * n + 1) ≤ d * (x + 1) := by
    calc
      _ ≤ (2 * a - 1) ^ (j - 1) := Nat.pow_le_pow_right (by omega) hexp
      _ ≤ ψ ha j := pow_le_ψ ha hjpos
      _ = d * (x + 1) := hj.symm
  have hbase : 4 * (n + 1) ≤ 2 * a - 1 := by dsimp [a]; omega
  let P := (2 * n) ^ (2 * n)
  have hP : 2 ≤ P := by
    have hpow : 2 * n ≤ (2 * n) ^ (2 * n) := Nat.le_self_pow (by omega) _
    dsimp [P]
    omega
  have hPpow : P ≤ (2 * a - 1) ^ (2 * n) :=
    Nat.pow_le_pow_left (by omega) _
  have hlarge : 4 * (n + 1) * P ≤ (2 * a - 1) ^ (2 * n + 1) := by
    calc
      _ ≤ (2 * a - 1) * (2 * a - 1) ^ (2 * n) := Nat.mul_le_mul hbase hPpow
      _ = (2 * a - 1) ^ (2 * n + 1) := by rw [pow_succ]; ring
  have htwice : 2 * P ≤ x + 1 := by
    apply Nat.le_of_mul_le_mul_left (c := d) _ hdpos
    calc
      d * (2 * P) = 4 * (n + 1) * P := by dsimp [d]; ring
      _ ≤ (2 * a - 1) ^ (2 * n + 1) := hlarge
      _ ≤ d * (x + 1) := hpower
  refine ⟨hT_square, hn, ?_⟩
  change P < x
  omega

/-- For every admissible first coordinate, (24) admits arbitrarily large `x`. -/
theorem exists_fiveSquareRadicand_square {k n : ℕ}
    (h : IsSquare (U (2 * k) n)) (bound : ℕ) :
    ∃ x : ℕ, bound ≤ x ∧ IsSquare (fiveSquareRadicand k n x) := by
  let T := U (2 * k) n
  let a := 2 * T - 1
  let d := 2 * (n + 1)
  have hT : n + 2 ≤ T := fiveSquare_U_lower k n
  have ha : 1 < a := by dsimp [a]; omega
  have hdpos : 0 < d := by dsimp [d]; positivity
  obtain ⟨j, hj, q, hq⟩ := exists_dvd_yn ha (by positivity : 0 < d * (bound + 1))
  have hypos : 0 < ψ ha j := ψ_pos_of_pos ha hj
  have hqpos : 0 < q := by
    by_contra hnot
    have : q = 0 := by omega
    rw [this, mul_zero] at hq
    change ψ ha j = 0 at hq
    omega
  let x := (bound + 1) * q - 1
  have hxsucc : x + 1 = (bound + 1) * q :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos _) hqpos)
  have hxbound : bound ≤ x := by
    have := Nat.le_mul_of_pos_right (bound + 1) hqpos
    dsimp [x]
    omega
  have hy : d * (x + 1) = ψ ha j := by
    rw [hxsucc]
    change d * ((bound + 1) * q) = yn ha j
    rw [hq]
    ring
  refine ⟨x, hxbound, (fiveSquareRadicand_isSquare_iff k n x).mpr ⟨h, ?_⟩⟩
  rw [fiveSquareSecond_eq_pell]
  change IsSquare ((a * a - 1) * (d * (x + 1)) ^ 2 + 1)
  rw [hy]
  exact square_of_ψ ha j

end JSWW1976
