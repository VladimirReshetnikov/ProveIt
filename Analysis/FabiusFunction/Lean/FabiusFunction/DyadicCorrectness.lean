import FabiusFunction.Arithmetic
import Mathlib.Tactic.FieldSimp

/-!
# Correctness infrastructure for the executable dyadic evaluator

This module discharges the structural part of the evaluator proof.  Once the
single-step dyadic recurrence from Proposition 10 is established, strong
induction proves that the terminating bit recursion agrees with the exact
closed formula at every point of the unit dyadic grid.  The representation API
also shows that neither a surplus inverse-power table bound nor a different
dyadic numerator/exponent presentation changes the computed value.
-/

set_option autoImplicit false

namespace Fabius

/-- Equation (32) vanishes at numerator `0`, where its sum over `Fin a` is
empty.  Used in `DyadicClosedForm`, `DyadicAnalytic`, and `GlobalDyadic`. -/
@[simp]
theorem fabiusDyadic_arg_zero (n : ℕ) : fabiusDyadic n 0 = 0 := by
  simp [fabiusDyadic]

/-! ## Inverse-power table -/

/-- The normalized recurrence used to append the next inverse-power value. -/
lemma halfMomentFabiusValue_succ (n : ℕ) :
    halfMomentFabiusValue (n + 1) =
      (∑ k : Fin (n + 1),
          halfMomentFabiusValue k.val /
            ((2 : ℚ) ^ ((n + 1).choose 2 - k.val.choose 2) *
              ((n + 1 - k.val + 1).factorial : ℚ))) /
        ((2 : ℚ) ^ (n + 1) - 1) := by
  rw [halfMomentFabiusValue, halfMoment_succ]
  simp only [halfMomentFabiusValue]
  have hpow : (1 : ℚ) < 2 ^ (n + 1) := by
    exact one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero n)
  have hden : (2 : ℚ) ^ (n + 1) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hpow)
  field_simp [hden]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k.val ≤ n + 1 := by omega
  have hchoose_le : k.val.choose 2 ≤ (n + 1).choose 2 := by
    exact Nat.choose_le_choose 2 hk_le
  have hsub : n + 1 - k.val + 1 = n + 2 - k.val := by omega
  have hpow_mul :
      (2 : ℚ) ^ k.val.choose 2 *
          2 ^ ((n + 1).choose 2 - k.val.choose 2) =
        2 ^ (n + 1).choose 2 := by
    rw [← pow_add, Nat.add_sub_of_le hchoose_le]
  have hchoose_fac := Nat.choose_mul_factorial_mul_factorial
    (n := n + 2) (k := k.val) (by omega : k.val ≤ n + 2)
  have hcoef :
      ((Nat.choose (n + 2) k.val : ℕ) : ℚ) * (k.val.factorial : ℚ) *
          ((n + 2 - k.val).factorial : ℚ) =
        (n + 2 : ℚ) * ((n + 1).factorial : ℚ) := by
    exact_mod_cast (show
      Nat.choose (n + 2) k.val * k.val.factorial * (n + 2 - k.val).factorial =
        (n + 2) * (n + 1).factorial by
      simpa [Nat.factorial_succ] using hchoose_fac)
  rw [hsub]
  field_simp
  calc
    _ = halfMoment k.val *
          (((Nat.choose (n + 2) k.val : ℕ) : ℚ) * (k.val.factorial : ℚ) *
            ((n + 2 - k.val).factorial : ℚ)) *
          ((2 : ℚ) ^ k.val.choose 2 *
            2 ^ ((n + 1).choose 2 - k.val.choose 2)) := by ring
    _ = halfMoment k.val * ((n + 2 : ℚ) * ((n + 1).factorial : ℚ)) *
          (2 : ℚ) ^ (n + 1).choose 2 := by rw [hcoef, hpow_mul]
    _ = _ := by
      push_cast
      ring

/-- The table for exponent `n` holds exactly `n + 1` entries, one for each
index from `0` to `n`. -/
@[simp]
lemma fabiusInversePowTwoTable_size (n : ℕ) :
    (fabiusInversePowTwoTable n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fabiusInversePowTwoTable, ih]

/-! ## Horner evaluation -/

/-- General loop invariant for the Horner evaluator. -/
lemma fabiusTaylorHorner_go_eq_sum
    (values : Array ℚ)
    (hzero : fabiusInversePowTwoTableValue values 0 = 1)
    (offset : ℚ) (m d : ℕ) :
    fabiusTaylorHorner.go values (d + m) offset m =
      ∑ k ∈ Finset.range (m + 1),
        (2 : ℚ) ^ (k * d + (k + 1).choose 2) *
          fabiusInversePowTwoTableValue values (m - k) * offset ^ k *
          (d.factorial : ℚ) / ((d + k).factorial : ℚ) := by
  induction m generalizing d with
  | zero =>
      simp [fabiusTaylorHorner.go.eq_1, hzero]
      rw [div_self (by positivity : (d.factorial : ℚ) ≠ 0)]
  | succ m ih =>
      rw [fabiusTaylorHorner.go.eq_2]
      have hnat : d + (m + 1) - m = d + 1 := by omega
      have hrat : ((d + (m + 1) : ℕ) : ℚ) - (m : ℚ) = (d + 1 : ℕ) := by
        push_cast
        ring
      have horder : d + (m + 1) = (d + 1) + m := by omega
      rw [hnat, hrat, horder, ih (d + 1)]
      have hdfact : (d.factorial : ℚ) ≠ 0 := by positivity
      conv_rhs => rw [Finset.sum_range_succ']
      norm_num [hdfact]
      rw [Finset.mul_sum, add_comm]
      apply congrArg₂ (· + ·) ?_ rfl
      apply Finset.sum_congr rfl
      intro k hk
      have hk_le : k ≤ m := by simpa using hk
      have hsub : m + 1 - (k + 1) = m - k := by omega
      have hchoose : (k + 1 + 1).choose 2 = (k + 1).choose 2 + (k + 1) := by
        rw [show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.add_comm]
      have hexponent :
          d + 1 + (k * (d + 1) + (k + 1).choose 2) =
            (k + 1) * d + (k + 1 + 1).choose 2 := by
        rw [hchoose]
        ring
      have hfactorial :
          ((d + 1).factorial : ℚ) = (d + 1 : ℚ) * (d.factorial : ℚ) := by
        simp [Nat.factorial_succ]
      have hdenIndex : d + (k + 1) = d + 1 + k := by omega
      have hpowers :
          (2 : ℚ) ^ (d + 1) * 2 ^ (k * (d + 1) + (k + 1).choose 2) =
            2 ^ ((k + 1) * d + (k + 1 + 1).choose 2) := by
        rw [← pow_add, hexponent]
      have hoffset : offset * offset ^ k = offset ^ (k + 1) := by
        rw [pow_succ']
      rw [hsub]
      field_simp
      calc
        _ = ((2 : ℚ) ^ (d + 1) *
              2 ^ (k * (d + 1) + (k + 1).choose 2)) *
              (offset * offset ^ k) *
              fabiusInversePowTwoTableValue values (m - k) *
              ((d + 1).factorial : ℚ) *
              ((d + (k + 1)).factorial : ℚ) := by ring
        _ = (2 : ℚ) ^ ((k + 1) * d + (k + 1 + 1).choose 2) *
              offset ^ (k + 1) *
              fabiusInversePowTwoTableValue values (m - k) *
              ((d + 1 : ℕ) : ℚ) * (d.factorial : ℚ) *
              ((d + 1 + k).factorial : ℚ) := by
          rw [hpowers, hoffset, hfactorial, hdenIndex]
          push_cast
          ring
        _ = _ := by
          push_cast
          ring

/-! ## Independence of dyadic representation -/

/-- Appending the next entry does not disturb the earlier ones: for `k ≤ n`
the optional lookups at index `k` in the tables for `n + 1` and `n` agree. -/
lemma fabiusInversePowTwoTable_succ_get (n k : ℕ) (hk : k ≤ n) :
    (fabiusInversePowTwoTable (n + 1))[k]? =
      (fabiusInversePowTwoTable n)[k]? := by
  have hne : k ≠ n + 1 := by omega
  rw [fabiusInversePowTwoTable]
  simp [Array.getElem?_push, fabiusInversePowTwoTable_size, hk, hne]

/-- Appending one entry to the inverse-power table leaves each Horner loop
step unchanged, provided the requested `order` fits in the smaller table
(`order ≤ n`) and the loop counter satisfies `m ≤ order`. -/
lemma fabiusTaylorHorner_go_table_succ (n order m : ℕ) (horder : order ≤ n)
    (hm : m ≤ order) (offset : ℚ) :
    fabiusTaylorHorner.go (fabiusInversePowTwoTable (n + 1)) order offset m =
      fabiusTaylorHorner.go (fabiusInversePowTwoTable n) order offset m := by
  induction m with
  | zero => rw [fabiusTaylorHorner.go.eq_1, fabiusTaylorHorner.go.eq_1]
  | succ m ih =>
      rw [fabiusTaylorHorner.go.eq_2, fabiusTaylorHorner.go.eq_2, ih (by omega)]
      unfold fabiusInversePowTwoTableValue
      rw [fabiusInversePowTwoTable_succ_get n (m + 1) (by omega)]

/-- Appending one entry to the inverse-power table leaves the whole Taylor
polynomial unchanged, provided the requested `order` already fits in the
smaller table. -/
lemma fabiusTaylorHorner_table_succ (n order : ℕ) (horder : order ≤ n)
    (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable (n + 1)) order offset =
      fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset := by
  unfold fabiusTaylorHorner
  exact fabiusTaylorHorner_go_table_succ n order order horder le_rfl offset

/-- Extending the inverse-power table by any number of entries leaves every
Horner subcomputation within the original table unchanged. -/
lemma fabiusTaylorHorner_go_table_add (n extra order m : ℕ)
    (horder : order ≤ n) (hm : m ≤ order) (offset : ℚ) :
    fabiusTaylorHorner.go (fabiusInversePowTwoTable (n + extra)) order offset m =
      fabiusTaylorHorner.go (fabiusInversePowTwoTable n) order offset m := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      calc
        fabiusTaylorHorner.go
              (fabiusInversePowTwoTable (n + (extra + 1))) order offset m =
            fabiusTaylorHorner.go
              (fabiusInversePowTwoTable (n + extra)) order offset m := by
          simpa [Nat.add_assoc] using
            fabiusTaylorHorner_go_table_succ (n + extra) order m
              (by omega) hm offset
        _ = fabiusTaylorHorner.go
              (fabiusInversePowTwoTable n) order offset m := ih

/-- Extending the inverse-power table by any number of entries does not change
a Taylor polynomial whose order already fits in the original table. -/
theorem fabiusTaylorHorner_table_add (n extra order : ℕ)
    (horder : order ≤ n) (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable (n + extra)) order offset =
      fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset := by
  unfold fabiusTaylorHorner
  exact fabiusTaylorHorner_go_table_add n extra order order horder le_rfl offset

/-- The Horner evaluator is independent of the chosen table bound, provided
both bounds contain every coefficient requested by the polynomial. -/
theorem fabiusTaylorHorner_table_eq_of_le (n maxExponent order : ℕ)
    (hn : n ≤ maxExponent) (horder : order ≤ n) (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable maxExponent) order offset =
      fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact fabiusTaylorHorner_table_add n extra order horder offset

/-- The Horner polynomial is independent of either table bound once both
tables contain all coefficients through `order`.  Unlike
`fabiusTaylorHorner_table_eq_of_le`, this statement does not require the two
table bounds themselves to be ordered. -/
theorem fabiusTaylorHorner_table_eq_of_order_le
    (n m order : ℕ) (hn : order ≤ n) (hm : order ≤ m) (offset : ℚ) :
    fabiusTaylorHorner (fabiusInversePowTwoTable n) order offset =
      fabiusTaylorHorner (fabiusInversePowTwoTable m) order offset := by
  rcases le_total n m with hnm | hmn
  · exact (fabiusTaylorHorner_table_eq_of_le n m order hnm hn offset).symm
  · exact fabiusTaylorHorner_table_eq_of_le m n order hmn hm offset

private theorem log2_two_mul (a : ℕ) (ha : a ≠ 0) :
    Nat.log2 (2 * a) = Nat.log2 a + 1 := by
  rw [Nat.log2_eq_log_two, mul_comm, Nat.log_mul_base Nat.one_lt_two ha,
    ← Nat.log2_eq_log_two]

private theorem fabiusDyadicUnitAux_refine_direct (n a : ℕ) :
    fabiusDyadicUnitAux (fabiusInversePowTwoTable (n + 1)) (n + 1) (2 * a) =
      fabiusDyadicUnitAux (fabiusInversePowTwoTable n) n a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
      cases a with
      | zero => simp [fabiusDyadicUnitAux]
      | succ a =>
          have hdouble : 2 * a + 1 + 1 = 2 * (a + 1) := by omega
          have hthreshold : 2 ^ (n + 1) ≤ 2 * (a + 1) ↔ 2 ^ n ≤ a + 1 := by
            rw [pow_succ]
            omega
          rw [show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
            fabiusDyadicUnitAux, fabiusDyadicUnitAux]
          split <;> rename_i hleft
          · rw [hdouble] at hleft
            rw [if_pos (hthreshold.mp hleft)]
          · have hright : ¬ 2 ^ n ≤ a + 1 := by
              rw [hdouble] at hleft
              intro hbad
              exact hleft (hthreshold.mpr hbad)
            rw [if_neg hright]
            dsimp only
            have hx0 : a + 1 ≠ 0 := by omega
            have hxlt : a + 1 < 2 ^ n := Nat.lt_of_not_ge hright
            have hloglt : Nat.log2 (a + 1) < n := by
              rw [Nat.log2_eq_log_two]
              exact Nat.log_lt_of_lt_pow hx0 hxlt
            have hpowle : 2 ^ Nat.log2 (a + 1) ≤ a + 1 := by
              rw [Nat.log2_eq_log_two]
              exact Nat.pow_log_le_self 2 hx0
            have hlogdouble : Nat.log2 (2 * a + 1 + 1) = Nat.log2 (a + 1) + 1 := by
              rw [hdouble, log2_two_mul (a + 1) hx0]
            have horder : n + 1 - (Nat.log2 (a + 1) + 1) =
                n - Nat.log2 (a + 1) := by omega
            have hrem : 2 * a + 1 + 1 - 2 ^ (Nat.log2 (a + 1) + 1) =
                2 * (a + 1 - 2 ^ Nat.log2 (a + 1)) := by
              rw [hdouble, pow_succ]
              omega
            have hrem_lt : a + 1 - 2 ^ Nat.log2 (a + 1) < a + 1 := by
              have : 0 < 2 ^ Nat.log2 (a + 1) := by positivity
              omega
            have hoffset :
                ((2 * (a + 1 - 2 ^ Nat.log2 (a + 1)) : ℕ) : ℚ) /
                    (2 : ℚ) ^ (n + 1) =
                  (a + 1 - 2 ^ Nat.log2 (a + 1) : ℕ) / (2 : ℚ) ^ n := by
              push_cast
              rw [pow_succ]
              ring
            rw [hlogdouble, horder, hrem, hoffset,
              fabiusTaylorHorner_table_succ n (n - Nat.log2 (a + 1))
                (Nat.sub_le n _) _,
              ih (a + 1 - 2 ^ Nat.log2 (a + 1)) hrem_lt]

private theorem fabiusDyadicUnit_refine_direct (n a : ℕ) :
    fabiusDyadicUnit (n + 1) (2 * a) = fabiusDyadicUnit n a := by
  by_cases ha : a = 0
  · subst a
    simp
  have h2a : 2 * a ≠ 0 := mul_ne_zero (by omega) ha
  have hthreshold : 2 ^ (n + 1) ≤ 2 * a ↔ 2 ^ n ≤ a := by
    rw [pow_succ]
    omega
  unfold fabiusDyadicUnit
  rw [if_neg h2a, if_neg ha]
  by_cases h : 2 ^ n ≤ a
  · rw [if_pos h, if_pos (hthreshold.mpr h)]
  · rw [if_neg h, if_neg (fun hbad => h (hthreshold.mp hbad))]
    exact fabiusDyadicUnitAux_refine_direct n a

/-- Refining a dyadic representation does not change the bounded value. -/
theorem fabiusDyadicValue_refine (n : ℕ) (a : ℤ) :
    fabiusDyadicValue (n + 1) (2 * a) = fabiusDyadicValue n a := by
  by_cases ha : a ≤ 0
  · have h2a : 2 * a ≤ 0 := by omega
    simp [fabiusDyadicValue, ha, h2a]
  · have ha0 : 0 ≤ a := (lt_of_not_ge ha).le
    have h2a : ¬ 2 * a ≤ 0 := by omega
    rw [fabiusDyadicValue, if_neg h2a, fabiusDyadicValue, if_neg ha]
    rw [Int.toNat_mul (by omega : (0 : ℤ) ≤ 2) ha0]
    exact fabiusDyadicUnit_refine_direct n a.toNat

/-- Refining a dyadic representation does not change the global value. -/
theorem extendedFabiusDyadicValue_refine (n : ℕ) (a : ℤ) :
    extendedFabiusDyadicValue (n + 1) (2 * a) =
      extendedFabiusDyadicValue n a := by
  by_cases ha : a ≤ 0
  · have h2a : 2 * a ≤ 0 := by omega
    simp [extendedFabiusDyadicValue, ha, h2a]
  · have ha0 : 0 ≤ a := (lt_of_not_ge ha).le
    have h2a : ¬ 2 * a ≤ 0 := by omega
    rw [extendedFabiusDyadicValue, if_neg h2a,
      extendedFabiusDyadicValue, if_neg ha]
    dsimp only
    rw [Int.toNat_mul (by omega : (0 : ℤ) ≤ 2) ha0]
    have htwo : (2 : ℤ).toNat = 2 := by decide
    rw [htwo]
    have hscale : 2 ^ (n + 1) = 2 * 2 ^ n := by
      rw [pow_succ]
      omega
    rw [hscale]
    have hblock : 2 * a.toNat / (2 * (2 * 2 ^ n)) =
        a.toNat / (2 * 2 ^ n) := by
      exact Nat.mul_div_mul_left a.toNat (2 * 2 ^ n) (by omega)
    have hresidue : 2 * a.toNat % (2 * (2 * 2 ^ n)) =
        2 * (a.toNat % (2 * 2 ^ n)) := by
      exact Nat.mul_mod_mul_left 2 a.toNat (2 * 2 ^ n)
    rw [hblock, hresidue]
    by_cases hres : a.toNat % (2 * 2 ^ n) ≤ 2 ^ n
    · have htwice : 2 * (a.toNat % (2 * 2 ^ n)) ≤ 2 * 2 ^ n :=
        Nat.mul_le_mul_left 2 hres
      rw [if_pos hres, if_pos htwice, fabiusDyadicUnit_refine_direct]
    · have htwice : ¬ 2 * (a.toNat % (2 * 2 ^ n)) ≤ 2 * 2 ^ n := by
        intro hbad
        exact hres ((Nat.mul_le_mul_left_iff (by omega : 0 < 2)).mp hbad)
      rw [if_neg hres, if_neg htwice, ← Nat.mul_sub_left_distrib,
        fabiusDyadicUnit_refine_direct]

/-- Iterated form of `fabiusDyadicValue_refine`: multiplying the numerator by
`2 ^ k` while raising the exponent by `k` leaves the bounded value unchanged.
This is the step used by `fabiusDyadicValue_eq_of_rat_eq` below. -/
theorem fabiusDyadicValue_refine_iter (n k : ℕ) (a : ℤ) :
    fabiusDyadicValue (n + k) ((2 : ℤ) ^ k * a) = fabiusDyadicValue n a := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        fabiusDyadicValue (n + (k + 1)) ((2 : ℤ) ^ (k + 1) * a) =
            fabiusDyadicValue (n + k) ((2 : ℤ) ^ k * a) := by
          simpa [pow_succ, Nat.add_assoc, mul_assoc, mul_comm, mul_left_comm] using
            fabiusDyadicValue_refine (n + k) ((2 : ℤ) ^ k * a)
        _ = fabiusDyadicValue n a := ih

/-- Iterated form of `extendedFabiusDyadicValue_refine`: multiplying the
numerator by `2 ^ k` while raising the exponent by `k` leaves the global
value unchanged.  This is the step used by
`extendedFabiusDyadicValue_eq_of_rat_eq` below. -/
theorem extendedFabiusDyadicValue_refine_iter (n k : ℕ) (a : ℤ) :
    extendedFabiusDyadicValue (n + k) ((2 : ℤ) ^ k * a) =
      extendedFabiusDyadicValue n a := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        extendedFabiusDyadicValue (n + (k + 1)) ((2 : ℤ) ^ (k + 1) * a) =
            extendedFabiusDyadicValue (n + k) ((2 : ℤ) ^ k * a) := by
          simpa [pow_succ, Nat.add_assoc, mul_assoc, mul_comm, mul_left_comm] using
            extendedFabiusDyadicValue_refine (n + k) ((2 : ℤ) ^ k * a)
        _ = extendedFabiusDyadicValue n a := ih

private theorem integer_eq_pow_mul_of_dyadic_eq (n k : ℕ) (a b : ℤ)
    (h : (a : ℚ) / (2 : ℚ) ^ n = (b : ℚ) / (2 : ℚ) ^ (n + k)) :
    b = (2 : ℤ) ^ k * a := by
  have hcross : (a : ℚ) * (2 : ℚ) ^ (n + k) =
      (b : ℚ) * (2 : ℚ) ^ n :=
    (div_eq_div_iff (by positivity) (by positivity)).mp h
  rw [pow_add] at hcross
  have hcancel : (a : ℚ) * (2 : ℚ) ^ k = b := by
    apply mul_left_cancel₀ (a := (2 : ℚ) ^ n) (by positivity)
    calc
      (2 : ℚ) ^ n * ((a : ℚ) * (2 : ℚ) ^ k) =
          (a : ℚ) * ((2 : ℚ) ^ n * (2 : ℚ) ^ k) := by ring
      _ = (b : ℚ) * (2 : ℚ) ^ n := hcross
      _ = (2 : ℚ) ^ n * b := by ring
  have : b = a * (2 : ℤ) ^ k := by exact_mod_cast hcancel.symm
  simpa [mul_comm] using this

/-- The bounded evaluator depends only on the represented rational number. -/
theorem fabiusDyadicValue_eq_of_rat_eq (n m : ℕ) (a b : ℤ)
    (h : (a : ℚ) / (2 : ℚ) ^ n = (b : ℚ) / (2 : ℚ) ^ m) :
    fabiusDyadicValue n a = fabiusDyadicValue m b := by
  rcases le_total n m with hnm | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hb : b = (2 : ℤ) ^ k * a := integer_eq_pow_mul_of_dyadic_eq n k a b h
    subst b
    exact (fabiusDyadicValue_refine_iter n k a).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have ha : a = (2 : ℤ) ^ k * b :=
      integer_eq_pow_mul_of_dyadic_eq m k b a h.symm
    subst a
    exact fabiusDyadicValue_refine_iter m k b

/-- The global evaluator depends only on the represented rational number. -/
theorem extendedFabiusDyadicValue_eq_of_rat_eq (n m : ℕ) (a b : ℤ)
    (h : (a : ℚ) / (2 : ℚ) ^ n = (b : ℚ) / (2 : ℚ) ^ m) :
    extendedFabiusDyadicValue n a = extendedFabiusDyadicValue m b := by
  rcases le_total n m with hnm | hmn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hb : b = (2 : ℤ) ^ k * a := integer_eq_pow_mul_of_dyadic_eq n k a b h
    subst b
    exact (extendedFabiusDyadicValue_refine_iter n k a).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have ha : a = (2 : ℤ) ^ k * b :=
      integer_eq_pow_mul_of_dyadic_eq m k b a h.symm
    subst a
    exact extendedFabiusDyadicValue_refine_iter m k b

/-- On nonnegative numerators, the signed-numerator bounded evaluator is
exactly the natural-numerator unit evaluator. -/
theorem fabiusDyadicValue_natCast (n a : ℕ) :
    fabiusDyadicValue n (a : ℤ) = fabiusDyadicUnit n a := by
  cases a with
  | zero => simp
  | succ a => simp [fabiusDyadicValue]

/-- The natural-numerator unit evaluator depends only on the represented
dyadic rational, even when the two denominator exponents are unrelated. -/
theorem fabiusDyadicUnit_eq_of_rat_eq (n m a b : ℕ)
    (h : (a : ℚ) / (2 : ℚ) ^ n = (b : ℚ) / (2 : ℚ) ^ m) :
    fabiusDyadicUnit n a = fabiusDyadicUnit m b := by
  have h' : ((a : ℤ) : ℚ) / (2 : ℚ) ^ n =
      ((b : ℤ) : ℚ) / (2 : ℚ) ^ m := by
    norm_num only [Int.cast_natCast]
    exact h
  simpa only [fabiusDyadicValue_natCast] using
    fabiusDyadicValue_eq_of_rat_eq n m (a : ℤ) (b : ℤ) h'

/-! ## Detection and rational wrappers -/

/-- `dyadicExponent?` succeeds exactly on dyadic rationals. -/
theorem dyadicExponent?_exists_iff (x : ℚ) :
    (∃ exponent, dyadicExponent? x = some exponent) ↔ IsDyadicRational x := by
  constructor
  · rintro ⟨exponent, hexponent⟩
    unfold dyadicExponent? at hexponent
    dsimp only at hexponent
    split at hexponent
    · rename_i hden
      injection hexponent with hexponent
      subst exponent
      exact ⟨_, hden⟩
    · simp at hexponent
  · rintro ⟨exponent, hden⟩
    refine ⟨x.den.log2, ?_⟩
    unfold dyadicExponent?
    dsimp only
    rw [if_pos]
    rw [hden, Nat.log2_eq_log_two, Nat.log_pow Nat.one_lt_two]

private theorem evalDyadic_eq_none_iff
    (evaluator : ℕ → ℤ → ℚ) (x : ℚ) :
    (match dyadicExponent? x with
      | none => none
      | some exponent => some (evaluator exponent x.num)) = none ↔
      ¬ IsDyadicRational x := by
  constructor
  · intro heval hdyadic
    obtain ⟨exponent, hexponent⟩ := (dyadicExponent?_exists_iff x).2 hdyadic
    simp [hexponent] at heval
  · intro hnondyadic
    split
    · rfl
    · rename_i exponent hexponent
      exact False.elim <| hnondyadic <|
        (dyadicExponent?_exists_iff x).1 ⟨exponent, hexponent⟩

/-- The rational bounded evaluator rejects exactly the non-dyadic inputs. -/
theorem evalFabiusDyadic_eq_none_iff (x : ℚ) :
    evalFabiusDyadic x = none ↔ ¬ IsDyadicRational x := by
  exact evalDyadic_eq_none_iff fabiusDyadicValue x

/-- The rational global evaluator rejects exactly the non-dyadic inputs. -/
theorem evalExtendedFabiusDyadic_eq_none_iff (x : ℚ) :
    evalExtendedFabiusDyadic x = none ↔ ¬ IsDyadicRational x := by
  exact evalDyadic_eq_none_iff extendedFabiusDyadicValue x

/-- The rational Rvachev evaluator rejects exactly the non-dyadic inputs. -/
theorem evalRvachevDyadic_eq_none_iff (x : ℚ) :
    evalRvachevDyadic x = none ↔ ¬ IsDyadicRational x := by
  exact evalDyadic_eq_none_iff rvachevDyadic x

/--
The exact single-step recurrence needed by the bit-recursive evaluator.

This is Proposition 10 specialized to positive dyadics in `(0,1]`, expressed
entirely in `ℚ`.
-/
def FabiusDyadicHasBitRecurrence (values : Array ℚ) (n : ℕ) : Prop :=
  ∀ a : ℕ, 0 < a → a ≤ 2 ^ n →
    let leadingExponent := Nat.log2 a
    let order := n - leadingExponent
    let remainder := a - 2 ^ leadingExponent
    let offset := (remainder : ℚ) / (2 : ℚ) ^ n
    fabiusDyadic n a =
      fabiusTaylorHorner values order offset - fabiusDyadic n remainder

/--
Assuming the single-step bit recurrence for `values` at exponent `n`, strong
induction on the numerator shows that the bit recursion agrees with equation
(32) at every numerator `a < 2 ^ n`.

The hypothesis is discharged for the precomputed table by
`fabiusInversePowTwoTable_hasBitRecurrence` in `DyadicClosedForm`.
-/
theorem fabiusDyadicUnitAux_eq_of_bitRecurrence
    (values : Array ℚ) (n : ℕ)
    (hrec : FabiusDyadicHasBitRecurrence values n) :
    ∀ a : ℕ, a < 2 ^ n →
      fabiusDyadicUnitAux values n a = fabiusDyadic n a := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
      intro ha
      cases a with
      | zero =>
          rw [fabiusDyadicUnitAux.eq_1]
          exact (fabiusDyadic_arg_zero n).symm
      | succ a =>
          have hpos : 0 < a + 1 := Nat.zero_lt_succ a
          have hnot_ge : ¬ 2 ^ n ≤ a + 1 := Nat.not_le.mpr ha
          rw [fabiusDyadicUnitAux.eq_2, if_neg hnot_ge]
          let leadingExponent := Nat.log2 (a + 1)
          let remainder := a + 1 - 2 ^ leadingExponent
          have hpow_pos : 0 < 2 ^ leadingExponent := by positivity
          have hrem_lt : remainder < a + 1 := by
            dsimp [remainder]
            exact Nat.sub_lt hpos hpow_pos
          have hrem_den : remainder < 2 ^ n := hrem_lt.trans ha
          change
            fabiusTaylorHorner values (n - Nat.log2 (a + 1))
                (((a + 1 - 2 ^ Nat.log2 (a + 1) : ℕ) : ℚ) / (2 : ℚ) ^ n) -
              fabiusDyadicUnitAux values n (a + 1 - 2 ^ Nat.log2 (a + 1)) =
            fabiusDyadic n (a + 1)
          rw [ih remainder hrem_lt hrem_den]
          exact (hrec (a + 1) hpos ha.le).symm

/--
The same recurrence hypothesis pins the right endpoint of the unit grid:
`fabiusDyadic n (2 ^ n) = 1`.

At `a = 2 ^ n` the leading exponent is `n`, so the recurrence contributes the
constant Horner term `1` minus the value at numerator `0`.
-/
theorem fabiusDyadic_unit_endpoint_of_bitRecurrence
    (values : Array ℚ) (n : ℕ)
    (hrec : FabiusDyadicHasBitRecurrence values n) :
    fabiusDyadic n (2 ^ n) = 1 := by
  have h := hrec (2 ^ n) (by positivity) le_rfl
  simpa [Nat.log2_eq_log_two, Nat.log_pow Nat.one_lt_two,
    fabiusTaylorHorner, fabiusTaylorHorner.go.eq_1, fabiusDyadic_arg_zero] using h

/--
All recursion and endpoint plumbing for correctness of `fabiusDyadicUnit`.
The only mathematical input is the exact single-step recurrence.
-/
theorem fabiusDyadicUnit_eq_fabiusDyadic_of_bitRecurrence
    (n a : ℕ) (ha : a ≤ 2 ^ n)
    (hrec : FabiusDyadicHasBitRecurrence (fabiusInversePowTwoTable n) n) :
    fabiusDyadicUnit n a = fabiusDyadic n a := by
  rcases ha.eq_or_lt with rfl | ha
  · rw [fabiusDyadicUnit_of_ge n (2 ^ n) le_rfl]
    exact (fabiusDyadic_unit_endpoint_of_bitRecurrence
      (fabiusInversePowTwoTable n) n hrec).symm
  · by_cases hzero : a = 0
    · subst a
      simp
    · rw [fabiusDyadicUnit]
      simp only [hzero, if_false, Nat.not_le.mpr ha, if_false]
      exact fabiusDyadicUnitAux_eq_of_bitRecurrence
        (fabiusInversePowTwoTable n) n hrec a ha

end Fabius
