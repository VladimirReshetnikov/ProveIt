import Diophantine.Paper1980.Grid100

/-!
# The rows of the next-state word

`EXPLORATION_FIXED_PROGRAM_ROUTING.md`, §5: *"Define `Next = (C − I + q F)/W`.  ...  Its rows
are the later `C` rows followed by the single final row `F`."*  In the counter note's form
(`route_divided`) the next-state word is `C/R + 2I·(q/R)`, so the same reading applies: the
quotient by the grid width shifts every row down by one, and the wraparound term sits in the
top row alone.

`row_div_pow` is the shift, `row_add_mul_pow` says a term supported at or above row `k`
leaves the rows below it alone, and `row_next` combines them: below the top row, the rows of
the next-state word are the later rows of the state word.  That is the last of the four
support facts the one-hot run consumes.
-/

namespace Jones1980

open Ternary

/-- Dividing by the grid width shifts every row down by one. -/
theorem row_div_pow (X m i : ℕ) : row (X / 3 ^ m) m i = row X m (i + 1) := by
  unfold row
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 2
  ring

/-- A term supported at or above row `k` leaves the rows below it alone. -/
theorem row_add_mul_pow {A c m i k : ℕ} (hik : i < k) :
    row (A + 3 ^ (m * k) * c) m i = row A m i := by
  have hk : m * k = m * i + m + m * (k - i - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = i + 1 + j := ⟨k - i - 1, by omega⟩
    have hj : i + 1 + j - i - 1 = j := by omega
    rw [hj]; ring
  have hd : (3 : ℕ) ^ (m * k) * c
      = 3 ^ (m * i) * (3 ^ m * (3 ^ (m * (k - i - 1)) * c)) := by
    rw [hk, pow_add, pow_add]; ring
  unfold row
  rw [hd, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

/-- **The rows of the next-state word.**  Below the top row, they are the later rows of the
state word. -/
theorem row_next {PC Iw m u i k : ℕ} (hik : i < k) :
    row (PC / 3 ^ m + 3 ^ (m * k) * Iw) m i = row PC m (i + 1) := by
  rw [row_add_mul_pow hik, row_div_pow]

end Jones1980
