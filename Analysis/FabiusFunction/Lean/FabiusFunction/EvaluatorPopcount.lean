import FabiusFunction.Arithmetic
import FabiusFunction.ThueMorseBitSupport
import FabiusFunction.DyadicClosedForm

/-!
# Interior-call complexity of the dyadic evaluator

The umbrella gap register's *Popcount complexity* subsection records two
competing candidates for the number `D(e, a)` of recursive calls of the
dyadic evaluator that enter its interior branch: the exact count
`D(e, a) = wt(a)` and the weaker bound `D(e, a) ≤ wt(a)`.  Its
obligation asks to define `D` in Lean, settle which statement matches
the executable recursion, and prove the relation to binary weight
including the endpoint and saturation branches.

`dyadicInteriorCalls` defines `D` by literally the branch structure of
`fabiusDyadicUnitAux`: zero at numerator `0`, zero on the saturation
branch `2^e ≤ a`, and one plus the count at the stripped remainder
`a - 2^{⌊log₂ a⌋}` on the interior branch — the same guards and the
same recursion argument, so each interior entry of the evaluator is
counted exactly once.

The resolution: **the exact count holds on the evaluator's entire
operating range**.  Each interior step strips precisely the leading
binary digit, so `D(e, a) = wt(a)` for every `a < 2^e` — including the
endpoint `a = 0`, where both sides vanish.  Only on the saturation
branch `2^e ≤ a`, where the evaluator answers `1` without recursing,
does the count drop to `0` and the exact statement degrade to the
inequality `D(e, a) ≤ wt(a)`.

* `dyadicInteriorCalls` — the count `D`.
* `dyadicInteriorCalls_eq_binaryWeight` — `D(e, a) = wt(a)` for
  `a < 2^e` (the exact-count candidate, settled affirmatively).
* `dyadicInteriorCalls_of_saturated` — `D(e, a) = 0` for `2^e ≤ a`.
* `dyadicInteriorCalls_le_binaryWeight` — `D(e, a) ≤ wt(a)`
  unconditionally (the weaker candidate, now a corollary).
* `binaryWeight_two_pow_sub_one`,
  `dyadicInteriorCalls_two_pow_sub_one` — the all-ones worst case
  `D(e, 2^e - 1) = e`.
-/

set_option autoImplicit false

namespace Fabius

/-- The number of recursive calls of the dyadic evaluator
`fabiusDyadicUnitAux` that enter the interior branch, defined by the
evaluator's own branch structure: the guards and the recursion argument
`a - 2 ^ Nat.log2 a` are those of the evaluator, so each interior entry
is counted exactly once. -/
def dyadicInteriorCalls (exponent : ℕ) : ℕ → ℕ
  | 0 => 0
  | a + 1 =>
      if 2 ^ exponent ≤ a + 1 then 0
      else 1 + dyadicInteriorCalls exponent (a + 1 - 2 ^ Nat.log2 (a + 1))
termination_by a => a
decreasing_by
  apply Nat.sub_lt (Nat.zero_lt_succ a)
  positivity

/-- The endpoint branch: numerator `0` makes no interior calls. -/
@[simp] theorem dyadicInteriorCalls_zero (e : ℕ) :
    dyadicInteriorCalls e 0 = 0 := by
  rw [dyadicInteriorCalls]

/-- The saturation branch: for `2^e ≤ a` the evaluator answers `1`
without recursing, so no interior calls are made. -/
theorem dyadicInteriorCalls_of_saturated (e a : ℕ) (h : 2 ^ e ≤ a) :
    dyadicInteriorCalls e a = 0 := by
  match a with
  | 0 =>
      have hpos : 0 < 2 ^ e := Nat.two_pow_pos e
      omega
  | m + 1 => rw [dyadicInteriorCalls, if_pos h]

/-- **The interior-call count is exactly the binary weight** on the
evaluator's operating range: `D(e, a) = wt(a)` for `a < 2^e`.  Each
interior step strips precisely the leading binary digit of the
numerator, so the recursion terminates after exactly one call per set
bit.  This settles the register's exact-count candidate affirmatively
(the endpoint `a = 0` included, both sides vanishing). -/
theorem dyadicInteriorCalls_eq_binaryWeight (e : ℕ) :
    ∀ a : ℕ, a < 2 ^ e → dyadicInteriorCalls e a = binaryWeight a := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    match a with
    | 0 =>
        intro _
        simp [binaryWeight]
    | m + 1 =>
        intro hlt
        rw [dyadicInteriorCalls, if_neg (not_le.mpr hlt)]
        set l := Nat.log2 (m + 1) with hl
        have hle : 2 ^ l ≤ m + 1 := by
          rw [hl, Nat.log2_eq_log_two]
          exact Nat.pow_log_le_self 2 (Nat.succ_ne_zero m)
        have hlt2 : m + 1 < 2 ^ (l + 1) := by
          rw [hl, Nat.log2_eq_log_two]
          exact Nat.lt_pow_succ_log_self (by norm_num) (m + 1)
        have hrem : m + 1 - 2 ^ l < 2 ^ l := by
          rw [pow_succ] at hlt2
          omega
        have hremlt : m + 1 - 2 ^ l < m + 1 := by
          have hpow : 0 < 2 ^ l := Nat.two_pow_pos l
          omega
        rw [ih _ hremlt (lt_trans hremlt hlt)]
        conv_rhs => rw [show m + 1 = 2 ^ l + (m + 1 - 2 ^ l) from by omega]
        rw [binaryWeight_add_pow_two l _ hrem]
        omega

/-- **The unconditional inequality** `D(e, a) ≤ wt(a)`: exact below
saturation, and trivial on the saturation branch where the count is
zero.  The register's weaker candidate is thus a corollary of the
exact one. -/
theorem dyadicInteriorCalls_le_binaryWeight (e a : ℕ) :
    dyadicInteriorCalls e a ≤ binaryWeight a := by
  rcases lt_or_ge a (2 ^ e) with h | h
  · exact le_of_eq (dyadicInteriorCalls_eq_binaryWeight e a h)
  · rw [dyadicInteriorCalls_of_saturated e a h]
    exact Nat.zero_le _

/-- The binary weight of the all-ones numeral: `wt(2^e - 1) = e`. -/
theorem binaryWeight_two_pow_sub_one (e : ℕ) :
    binaryWeight (2 ^ e - 1) = e := by
  induction e with
  | zero => simp [binaryWeight]
  | succ n ih =>
      have hsplit : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
        have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
        rw [pow_succ]
        omega
      rw [hsplit, binaryWeight_two_mul_add_one, ih]

/-- **The worst case of the evaluator's interior recursion**: the
all-ones numerator `2^e - 1` makes exactly `e` interior calls — the
maximum possible below saturation, since `wt(a) ≤ e` there. -/
theorem dyadicInteriorCalls_two_pow_sub_one (e : ℕ) :
    dyadicInteriorCalls e (2 ^ e - 1) = e := by
  have hlt : 2 ^ e - 1 < 2 ^ e := by
    have hpos : 0 < 2 ^ e := Nat.two_pow_pos e
    omega
  rw [dyadicInteriorCalls_eq_binaryWeight e _ hlt,
    binaryWeight_two_pow_sub_one]

end Fabius
