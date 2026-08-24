import Sharma2012.CountingConsequences
import RamseyPaperCommon.CountConsequences
import Mathlib

/-!
# Lower-bound consequences for Sharma's counting function

This module isolates the interval induction and asymptotic arguments from
Section 3.  Several intermediate statements are intentionally exposed in a
more reusable form than the paper-specific wrappers.
-/

set_option autoImplicit false

noncomputable section

open Filter

namespace LeanProofs.Sharma2012

/-- Sharma's `theta` and the Davis count are the same finite cardinality. -/
theorem theta_eq_davis_count (n : Nat) :
    theta n = LeanProofs.DavisEntringerGrahamSimmons1977.M n := by
  rw [LeanProofs.RamseyPaperCommon.sharma_theta_eq_M,
    ← LeanProofs.RamseyPaperCommon.davis_M_eq_lesaulnier_M]

/-- The exact certified values of `theta(1), ..., theta(20)`. -/
theorem theta_values_through_twenty :
    List.ofFn (fun i : Fin 20 => theta ((i : Nat) + 1)) =
      [1, 2, 4, 10, 20, 48, 104, 282, 496, 1066,
        2460, 6128, 12840, 29380, 74904, 212728, 368016,
        659296, 1371056, 2937136] := by
  simpa only [theta_eq_davis_count] using
    (show List.ofFn (fun i : Fin 20 =>
        LeanProofs.DavisEntringerGrahamSimmons1977.M ((i : Nat) + 1)) =
      [1, 2, 4, 10, 20, 48, 104, 282, 496, 1066,
        2460, 6128, 12840, 29380, 74904, 212728, 368016,
        659296, 1371056, 2937136] from
      LeanProofs.DavisEntringerGrahamSimmons1977.table_1_holds)

/-- The finite base interval used in Theorem 3.1. -/
theorem theta_ge_two_pow_on_ten_nineteen (n : Nat)
    (hlo : 10 ≤ n) (hhi : n < 20) : 2 ^ n ≤ theta n := by
  have htable := theta_values_through_twenty
  have hentry := congrArg (fun values : List Nat => values[n - 1]?) htable
  interval_cases n <;> norm_num at hentry ⊢ <;> omega

/-- One application of Sharma's even recurrence doubles both the interval
index and the excess exponent over `2^n`. -/
theorem theta_even_amplify (k r : Nat) (hk : 1 ≤ k)
    (h : 2 ^ (k + r - 1) ≤ theta k) :
    2 ^ (2 * k + 2 * r - 1) ≤ theta (2 * k) := by
  have hkr : 1 ≤ k + r := by omega
  have hexp : 2 * k + 2 * r - 1 =
      (k + r - 1) + (k + r - 1) + 1 := by omega
  calc
    2 ^ (2 * k + 2 * r - 1) =
        2 ^ (k + r - 1) * 2 ^ (k + r - 1) * 2 := by
      rw [hexp, pow_add, pow_add]
      norm_num
    _ ≤ theta k * theta k * 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul h h) (le_refl 2)
    _ = 2 * theta k ^ 2 := by ring
    _ ≤ theta (2 * k) := inequality_1_holds k hk

/-- One application of Sharma's odd recurrence combines adjacent lower
bounds with the corresponding excess exponent. -/
theorem theta_odd_amplify (k r : Nat) (hk : 1 ≤ k)
    (h0 : 2 ^ (k + r - 1) ≤ theta k)
    (h1 : 2 ^ (k + 1 + r - 1) ≤ theta (k + 1)) :
    2 ^ ((2 * k + 1) + 2 * r - 1) ≤ theta (2 * k + 1) := by
  have hkr : 1 ≤ k + r := by omega
  have hexp : (2 * k + 1) + 2 * r - 1 =
      (k + r - 1) + (k + 1 + r - 1) + 1 := by omega
  calc
    2 ^ ((2 * k + 1) + 2 * r - 1) =
        2 ^ (k + r - 1) * 2 ^ (k + 1 + r - 1) * 2 := by
      rw [hexp, pow_add, pow_add]
      norm_num
    _ ≤ theta k * theta (k + 1) * 2 :=
      Nat.mul_le_mul (Nat.mul_le_mul h0 h1) (le_refl 2)
    _ = 2 * theta k * theta (k + 1) := by ring
    _ ≤ theta (2 * k + 1) := inequality_2_holds k hk

/-- **Theorem 3.1.** The iterated interval lower bounds. -/
theorem theorem_3_1_holds : theorem_3_1 := by
  intro p
  induction p with
  | zero =>
      intro n hlo hhi
      simpa using theta_ge_two_pow_on_ten_nineteen n (by norm_num at hlo; omega)
        (by norm_num at hhi; omega)
  | succ p ih =>
      intro n hlo hhi
      let L := 5 * 2 ^ (p + 2)
      have hlo' : L ≤ n := by simpa [L] using hlo
      have hhi' : n < 2 * L := by
        dsimp only [L]
        rw [show p + 3 = (p + 2) + 1 by omega, pow_succ] at hhi
        omega
      have hpowSucc : 2 ^ (p + 1) = 2 * 2 ^ p := by
        rw [pow_succ]
        ring
      have heven : ∀ m : Nat, L ≤ m → m < 2 * L → Even m →
          2 ^ (m + 2 ^ (p + 1) - 1) ≤ theta m := by
        intro m hmlo hmhi hmeven
        obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp hmeven
        have hklo : 5 * 2 ^ (p + 1) ≤ k := by
          dsimp only [L] at hmlo
          rw [show p + 2 = (p + 1) + 1 by omega, pow_succ] at hmlo
          omega
        have hkhi : k < 5 * 2 ^ (p + 2) := by
          dsimp only [L] at hmhi
          omega
        have hprev := ih k hklo hkhi
        have hamp := theta_even_amplify k (2 ^ p) (by omega) hprev
        simpa only [hpowSucc] using hamp
      by_cases hneven : Even n
      · exact heven n hlo' hhi' hneven
      · have hnodd : Odd n := Nat.not_even_iff_odd.mp hneven
        obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hnodd
        have hklo : 5 * 2 ^ (p + 1) ≤ k := by
          dsimp only [L] at hlo'
          rw [show p + 2 = (p + 1) + 1 by omega, pow_succ] at hlo'
          omega
        have hkhi : k < 5 * 2 ^ (p + 2) := by
          dsimp only [L] at hhi'
          omega
        have hkpos : 1 ≤ k := by omega
        have h0 := ih k hklo hkhi
        have h1 : 2 ^ (k + 1 + 2 ^ p - 1) ≤ theta (k + 1) := by
          by_cases hk1 : k + 1 < 5 * 2 ^ (p + 2)
          · exact ih (k + 1) (by omega) hk1
          · have hk1eq : k + 1 = L := by
              dsimp only [L] at hhi' ⊢
              omega
            have hLeven : Even L := by
              apply even_iff_exists_two_mul.mpr
              refine ⟨5 * 2 ^ (p + 1), ?_⟩
              dsimp only [L]
              rw [show p + 2 = (p + 1) + 1 by omega, pow_succ]
              ring
            have hstrong := heven (k + 1) (by omega) (by omega)
              (by simpa only [hk1eq] using hLeven)
            have hbonus : 2 ^ p ≤ 2 ^ (p + 1) :=
              pow_le_pow_right' (by omega) (by omega)
            have hexp : k + 1 + 2 ^ p - 1 ≤
                k + 1 + 2 ^ (p + 1) - 1 := by omega
            exact (pow_le_pow_right' (by omega) hexp).trans hstrong
        have hamp := theta_odd_amplify k (2 ^ p) hkpos h0 h1
        simpa only [hpowSucc] using hamp

/-- The elementary inequality behind the conversion from Theorem 3.1's
excess exponent `2^q - 1` to any prescribed excess exponent `q`. -/
theorem nat_lt_two_pow (q : Nat) : q < 2 ^ q := by
  induction q with
  | zero => norm_num
  | succ q ih =>
      rw [pow_succ]
      have hpos : 0 < 2 ^ q := pow_pos (by norm_num) q
      omega

/-- A convenient global form of Theorem 3.1: once `n` is beyond the first
interval belonging to `q`, `theta n` has at least the fixed excess factor
`2^q` over the elementary bound `2^n`.

Unlike the paper's interval formulation, this version is closed under the
halving operations used in the proof of Theorem 3.2. -/
theorem theta_ge_two_pow_add (q n : Nat)
    (hn : 5 * 2 ^ (q + 1) <= n) : 2 ^ (n + q) <= theta n := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      let L := 5 * 2 ^ (q + 1)
      have hnL : L <= n := by simpa [L] using hn
      by_cases hbase : n < 2 * L
      · have hinterval : n < 5 * 2 ^ (q + 2) := by
          dsimp only [L] at hbase
          rw [show q + 2 = (q + 1) + 1 by omega, pow_succ]
          omega
        have h31 := theorem_3_1_holds q n hn hinterval
        have hq : q <= 2 ^ q - 1 := by
          have := nat_lt_two_pow q
          omega
        exact (pow_le_pow_right' (by omega) (by omega)).trans h31
      · by_cases heven : Even n
        · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp heven
          have hkL : L <= k := by omega
          have hkpos : 1 <= k := by
            have hLpos : 0 < L := by
              dsimp only [L]
              positivity
            omega
          have hklt : k < 2 * k := by omega
          have hprev := ih k hklt (by simpa [L] using hkL)
          have hamp := theta_even_amplify k (q + 1) hkpos (by
            simpa [Nat.add_assoc] using hprev)
          exact (pow_le_pow_right' (by omega) (by omega)).trans hamp
        · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
          obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hodd
          have hkL : L <= k := by omega
          have hkpos : 1 <= k := by
            have hLpos : 0 < L := by
              dsimp only [L]
              positivity
            omega
          have hklt : k < 2 * k + 1 := by omega
          have hk1lt : k + 1 < 2 * k + 1 := by omega
          have h0 := ih k hklt (by simpa [L] using hkL)
          have h1 := ih (k + 1) hk1lt (by simpa [L] using (show L <= k + 1 by omega))
          have hamp := theta_odd_amplify k (q + 1) hkpos
            (by simpa [Nat.add_assoc] using h0)
            (by
              have hexp : k + 1 + (q + 1) - 1 = k + 1 + q := by omega
              simpa only [hexp] using h1)
          exact (pow_le_pow_right' (by omega) (by omega)).trans hamp

/-- The normalized sequence used in Sharma's proof of Theorem 3.2.  The
extra power of `n` is what turns a uniform positive lower bound into a
quantity tending to infinity. -/
def normalizedTheta (q n : Nat) : Real :=
  (theta n : Real) / ((n : Real) ^ (q + 1) * (2 : Real) ^ n)

/-- The normalized sequence does not decrease when an index is doubled,
once the global fixed-excess lower bound is available. -/
theorem normalizedTheta_le_even (q n : Nat)
    (hn : 5 * 2 ^ (q + 1) <= n) :
    normalizedTheta q n <= normalizedTheta q (2 * n) := by
  have hnpos : 0 < n := by
    have hthreshold : 0 < 5 * 2 ^ (q + 1) := by positivity
    omega
  have hlower : 2 ^ q * 2 ^ n <= theta n := by
    simpa only [pow_add, Nat.mul_comm] using theta_ge_two_pow_add q n hn
  have hrec := inequality_1_holds n hnpos
  have hcross :
      theta n * ((2 * n) ^ (q + 1) * 2 ^ (2 * n)) <=
        theta (2 * n) * (n ^ (q + 1) * 2 ^ n) := by
    calc
      theta n * ((2 * n) ^ (q + 1) * 2 ^ (2 * n)) =
          (2 * theta n * n ^ (q + 1) * 2 ^ n) * (2 ^ q * 2 ^ n) := by
        rw [mul_pow, pow_succ, show 2 * n = n + n by omega, pow_add]
        ring
      _ <= (2 * theta n * n ^ (q + 1) * 2 ^ n) * theta n :=
        Nat.mul_le_mul_left _ hlower
      _ = (2 * theta n ^ 2) * (n ^ (q + 1) * 2 ^ n) := by ring
      _ <= theta (2 * n) * (n ^ (q + 1) * 2 ^ n) :=
        Nat.mul_le_mul_right _ hrec
  unfold normalizedTheta
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  exact_mod_cast hcross

/-- The corresponding normalized monotonicity for an odd index.  As in the
paper, the comparison is with the upper half-index `n + 1`. -/
theorem normalizedTheta_le_odd (q n : Nat)
    (hn : 5 * 2 ^ (q + 1) <= n) :
    normalizedTheta q (n + 1) <= normalizedTheta q (2 * n + 1) := by
  have hnpos : 0 < n := by
    have hthreshold : 0 < 5 * 2 ^ (q + 1) := by positivity
    omega
  have hlower : 2 ^ q * 2 ^ n <= theta n := by
    simpa only [pow_add, Nat.mul_comm] using theta_ge_two_pow_add q n hn
  have hrec := inequality_2_holds n hnpos
  have hbasePow : (2 * n + 1) ^ (q + 1) <= (2 * (n + 1)) ^ (q + 1) := by
    exact pow_le_pow_left' (by omega) (q + 1)
  have hcross :
      theta (n + 1) * ((2 * n + 1) ^ (q + 1) * 2 ^ (2 * n + 1)) <=
        theta (2 * n + 1) * ((n + 1) ^ (q + 1) * 2 ^ (n + 1)) := by
    calc
      theta (n + 1) * ((2 * n + 1) ^ (q + 1) * 2 ^ (2 * n + 1)) <=
          theta (n + 1) * ((2 * (n + 1)) ^ (q + 1) * 2 ^ (2 * n + 1)) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hbasePow)
      _ = (4 * theta (n + 1) * (n + 1) ^ (q + 1) * 2 ^ n) *
          (2 ^ q * 2 ^ n) := by
        rw [mul_pow, pow_succ, show 2 * n + 1 = n + n + 1 by omega,
          pow_succ, pow_add]
        ring
      _ <= (4 * theta (n + 1) * (n + 1) ^ (q + 1) * 2 ^ n) * theta n :=
        Nat.mul_le_mul_left _ hlower
      _ = (2 * theta n * theta (n + 1)) *
          ((n + 1) ^ (q + 1) * 2 ^ (n + 1)) := by
        rw [pow_succ]
        ring
      _ <= theta (2 * n + 1) * ((n + 1) ^ (q + 1) * 2 ^ (n + 1)) :=
        Nat.mul_le_mul_right _ hrec
  unfold normalizedTheta
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  exact_mod_cast hcross

/-- The first index at which the fixed excess `q` is available globally. -/
def asymptoticThreshold (q : Nat) : Nat := 5 * 2 ^ (q + 1)

/-- An explicit positive lower bound for `normalizedTheta q`.  Its numerical
value is deliberately crude; being explicit avoids a noncomputable finite
minimum and makes the strengthening reusable. -/
def normalizedThetaLower (q : Nat) : Real :=
  1 / (((2 * asymptoticThreshold q : Nat) : Real) ^ (q + 1) *
    (2 : Real) ^ (2 * asymptoticThreshold q))

theorem normalizedThetaLower_pos (q : Nat) : 0 < normalizedThetaLower q := by
  unfold normalizedThetaLower asymptoticThreshold
  positivity

/-- Sharma's halving argument, in a strengthened quantitative form: the
normalized sequence has one explicit positive lower bound at every index
beyond `asymptoticThreshold q`. -/
theorem normalizedThetaLower_le (q n : Nat)
    (hn : asymptoticThreshold q <= n) :
    normalizedThetaLower q <= normalizedTheta q n := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hbase : n < 2 * asymptoticThreshold q
      · have hnpos : 0 < n := by
          have hthreshold : 0 < asymptoticThreshold q := by
            unfold asymptoticThreshold
            positivity
          omega
        have htheta : 1 <= theta n := by
          have hpow := theta_ge_two_pow_add q n (by
            simpa [asymptoticThreshold] using hn)
          have : 1 <= 2 ^ (n + q) := Nat.one_le_two_pow
          omega
        have hdenom :
            (n : Real) ^ (q + 1) * (2 : Real) ^ n <=
              ((2 * asymptoticThreshold q : Nat) : Real) ^ (q + 1) *
                (2 : Real) ^ (2 * asymptoticThreshold q) := by
          have hnNat : n <= 2 * asymptoticThreshold q := by omega
          have hnReal : (n : Real) <= (2 * asymptoticThreshold q : Nat) := by
            exact_mod_cast hnNat
          exact mul_le_mul (pow_le_pow_left₀ (by positivity) hnReal (q + 1))
            (pow_le_pow_right₀ (by norm_num) hnNat) (by positivity) (by positivity)
        unfold normalizedThetaLower normalizedTheta
        exact div_le_div₀ (by positivity) (by exact_mod_cast htheta)
          (mul_pos (pow_pos (by exact_mod_cast hnpos) _) (pow_pos (by norm_num) _)) hdenom
      · by_cases heven : Even n
        · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp heven
          have hk : asymptoticThreshold q <= k := by omega
          have hklt : k < 2 * k := by
            have : 0 < asymptoticThreshold q := by
              unfold asymptoticThreshold
              positivity
            omega
          exact (ih k hklt hk).trans (normalizedTheta_le_even q k (by
            simpa [asymptoticThreshold] using hk))
        · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
          obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hodd
          have hk : asymptoticThreshold q <= k := by omega
          have hk1lt : k + 1 < 2 * k + 1 := by
            have : 0 < asymptoticThreshold q := by
              unfold asymptoticThreshold
              positivity
            omega
          exact (ih (k + 1) hk1lt (by omega)).trans
            (normalizedTheta_le_odd q k (by
              simpa [asymptoticThreshold] using hk))

/-- A strengthened natural-exponent form of Theorem 3.2. -/
theorem theta_superpolynomial_nat (q : Nat) :
    Tendsto
      (fun n : Nat =>
        (theta n : Real) / ((n : Real) ^ q * (2 : Real) ^ n))
      atTop atTop := by
  have hc : 0 < normalizedThetaLower q := normalizedThetaLower_pos q
  have hlinear : Tendsto
      (fun n : Nat => normalizedThetaLower q * (n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  refine tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [eventually_ge_atTop (asymptoticThreshold q)] with n hn
  have hnpos : 0 < n := by
    have : 0 < asymptoticThreshold q := by
      unfold asymptoticThreshold
      positivity
    omega
  have hnorm := normalizedThetaLower_le q n hn
  have hmul : normalizedThetaLower q * (n : Real) <=
      (n : Real) * normalizedTheta q n := by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hnorm (show (0 : Real) <= n by positivity)
  calc
    normalizedThetaLower q * (n : Real) <=
        (n : Real) * normalizedTheta q n := hmul
    _ = (theta n : Real) / ((n : Real) ^ q * (2 : Real) ^ n) := by
      unfold normalizedTheta
      rw [pow_succ]
      have hn0 : (n : Real) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos)
      field_simp [hn0]

/-- **Theorem 3.2.** Sharma's superpolynomial improvement over `2^n`.
The natural-exponent strengthening above also handles negative integer
exponents by monotonicity of integer powers on bases at least one. -/
theorem theorem_3_2_holds : theorem_3_2 := by
  intro p
  let q := p.toNat
  have hnat := theta_superpolynomial_nat q
  refine tendsto_atTop_mono' atTop ?_ hnat
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpq : p <= (q : Int) := by
    dsimp only [q]
    cases p with
    | ofNat k => simp
    | negSucc k =>
        simp
        omega
  have hnreal : (1 : Real) <= n := by exact_mod_cast hn
  have hpow : (n : Real) ^ p <= (n : Real) ^ (q : Int) :=
    zpow_le_zpow_right₀ hnreal hpq
  have hdenom : (n : Real) ^ p * (2 : Real) ^ n <=
      (n : Real) ^ (q : Int) * (2 : Real) ^ n := by gcongr
  have hdiv := div_le_div_of_nonneg_left (show (0 : Real) <= theta n by positivity)
    (mul_pos (zpow_pos (by positivity) p) (pow_pos (by norm_num) n)) hdenom
  simpa only [zpow_natCast] using hdiv

/-- The exact finite verification underlying Corollary 3.2.1. -/
theorem normalizedTheta_one_tenth_base (n : Nat) (hn : 0 < n) (hn20 : n < 20) :
    (1 : Real) / 10 <= normalizedTheta 0 n := by
  have htable := theta_values_through_twenty
  have hentry := congrArg (fun values : List Nat => values[n - 1]?) htable
  interval_cases n <;> norm_num at hentry ⊢ <;>
    norm_num [normalizedTheta, hentry]

/-- The quantitative invariant from the corollary, stated directly for the
normalized sequence. -/
theorem normalizedTheta_one_tenth (n : Nat) (hn : 0 < n) :
    (1 : Real) / 10 <= normalizedTheta 0 n := by
  revert hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hsmall : n < 20
      · exact normalizedTheta_one_tenth_base n hn hsmall
      · by_cases heven : Even n
        · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp heven
          have hk : 10 <= k := by omega
          exact (ih k (by omega) (by omega)).trans
            (normalizedTheta_le_even 0 k (by norm_num; omega))
        · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
          obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hodd
          have hk : 10 <= k := by omega
          exact (ih (k + 1) (by omega) (by omega)).trans
            (normalizedTheta_le_odd 0 k (by norm_num; omega))

/-- **Corollary 3.2.1.** The concrete lower bound at every positive index. -/
theorem corollary_3_2_1_holds : corollary_3_2_1 := by
  intro n hn
  have hnorm := normalizedTheta_one_tenth n hn
  have hdenom : 0 < (n : Real) ^ (0 + 1) * (2 : Real) ^ n := by positivity
  unfold normalizedTheta at hnorm
  have hmul := (le_div_iff₀ hdenom).mp hnorm
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

end LeanProofs.Sharma2012
