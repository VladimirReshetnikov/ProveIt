import Diophantine.Paper1980.Rows100

/-!
# The row transport

`EXPLORATION_FIXED_PROGRAM_ROUTING.md`, §5: *"Every base-`W` row of `C` is a subword of `S`
and is therefore at most `S`.  By (2), `K·(each C row) ≤ K S < W`.  Consequently the integer
product `K C` has no carry between time rows."*

That is what this module makes precise.  Two numeric facts from the fixed grid do the work:
the marker times the state word fits inside a row, so a row's *target* columns stay inside
that row; and eight times the table times the state word fits inside a row, so a row's
doubled table output does too.  With those, the product of the table and a one-hot history
splits row by row, and the projection of `Controller100` reads each row on its own.

`dg_target_row` is the transport at a target column: the digit of `K·C` at column `j` of row
`i` is `2` exactly when `j` is the successor of the state selected in row `i`.
`dg_marker_row`, `dg_sgn_row` and `dg_zreq_row` read the marker and the two ports the same
way.  What remains for §5 is to match these against `g·Next` and the junk, which is where
the one-hot induction closes.
-/

namespace Jones1980

open Ternary

/-- Doubling a Boolean word doubles every digit. -/
theorem Ternary.dg_two_mul {X p : ℕ} (hX : Bool3 X) : Ternary.dg (2 * X) p = 2 * dg X p := by
  have h1 : 2 * X / 3 ^ p = 2 * (X / 3 ^ p) := Ternary.two_mul_div hX
  have h2 : X / 3 ^ p % 3 ≤ 1 := hX p
  unfold Ternary.dg
  rw [h1]
  omega

section Transport

variable {P : Controller} {Zon B0 : ℕ}
  {x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y : ℕ}
  {e m u : ℕ}
  (hOk : (P.rom Zon B0).Ok)
  (hP : Pos100 x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k o s w τ η ζ γ y)
  (hS : Sys100 (P.rom Zon B0) x q J W H v t A0 A1 Kp Km D α R PC PV β z r a c d f h i j k
    o s w τ η ζ γ y)
  (hG : Geometry100 H R q e m u)

include hOk hP hS hG

/-- The target column of a row lies inside the row, because the marker times the state word
fits inside a row. -/
theorem target_lt_width {jj : ℕ} (hj : jj < P.n) : P.mark + coord jj < m := by
  have hgS := gS_lt_R hOk hP hS
  have h1 : (3 : ℕ) ^ coord jj ≤ P.romS := P.pow_coord_le_romS hj
  have h2 : (3 : ℕ) ^ (P.mark + coord jj) < 3 ^ m := by
    rw [pow_add]
    calc 3 ^ P.mark * 3 ^ coord jj ≤ P.romg * P.romS := Nat.mul_le_mul (le_refl _) h1
      _ < R := hgS
      _ = 3 ^ m := hG.hR
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h2

/-- The marker column lies inside the row. -/
theorem marker_lt_width100 : P.mark < m := by
  have h := target_lt_width hOk hP hS hG (show 0 < P.n by have := P.two_le; omega)
  have h1 : coord 0 = 1 := rfl
  omega

/-- A row's doubled table output fits inside the row. -/
theorem row_fits {st : ℕ} (hst : st < P.n) : 2 * (3 ^ coord st * P.romK) < 3 ^ m := by
  have h8 := eight_KS_lt_R hOk hP hS
  have hbridge : (P.rom Zon B0).K * (P.rom Zon B0).S = P.romK * P.romS := rfl
  have h1 : (3 : ℕ) ^ coord st ≤ P.romS := P.pow_coord_le_romS hst
  have h2 : P.romK * 3 ^ coord st ≤ P.romK * P.romS := Nat.mul_le_mul_left _ h1
  have h3 : R = 3 ^ m := hG.hR
  have h4 : 3 ^ coord st * P.romK = P.romK * 3 ^ coord st := Nat.mul_comm _ _
  omega

/-- The product of the table with a one-hot history splits row by row. -/
theorem romK_mul_history {sf : ℕ → ℕ} :
    P.romK * (2 * rowsum (fun i => 3 ^ coord (sf i)) m u)
      = rowsum (fun k => 2 * (3 ^ coord (sf k) * P.romK)) m u := by
  unfold rowsum
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **The row transport at a target column.**  The digit of `K · C` at column `j` of row `i`
is `2` exactly when `j` is the successor of the state selected in row `i`. -/
theorem dg_target_row {sf : ℕ → ℕ} (hsf : ∀ i, sf i < P.n) {ii jj : ℕ}
    (hi : ii < u) (hj : jj < P.n) :
    Ternary.dg (P.romK * (2 * rowsum (fun i => 3 ^ coord (sf i)) m u))
        (m * ii + (P.mark + coord jj))
      = if jj = P.f (sf ii) then 2 else 0 := by
  have hfit : ∀ k, 2 * (3 ^ coord (sf k) * P.romK) < 3 ^ m :=
    fun k => row_fits hOk hP hS hG (hsf k)
  rw [romK_mul_history hOk hP hS hG, ← Ternary.dg_row _ ii (target_lt_width hOk hP hS hG hj),
    row_rowsum hfit u ii hi, Ternary.dg_two_mul (P.romK_bool.mul_pow _),
    P.dg_romK_shift (hsf ii) hj]
  split <;> norm_num

/-- The marker term counts the step, row by row. -/
theorem dg_marker_row {sf : ℕ → ℕ} (hsf : ∀ i, sf i < P.n) {ii : ℕ} (hi : ii < u) :
    Ternary.dg (P.romK * (2 * rowsum (fun i => 3 ^ coord (sf i)) m u)) (m * ii + P.mark) = 2 := by
  have hfit : ∀ k, 2 * (3 ^ coord (sf k) * P.romK) < 3 ^ m :=
    fun k => row_fits hOk hP hS hG (hsf k)
  rw [romK_mul_history hOk hP hS hG, ← Ternary.dg_row _ ii (marker_lt_width100 hOk hP hS hG),
    row_rowsum hfit u ii hi, Ternary.dg_two_mul (P.romK_bool.mul_pow _),
    P.dg_romK_shift_mark (hsf ii)]

/-- The sign port carries the sign label, row by row. -/
theorem dg_sgn_row {sf : ℕ → ℕ} (hsf : ∀ i, sf i < P.n) {ii : ℕ} (hi : ii < u) :
    Ternary.dg (P.romK * (2 * rowsum (fun i => 3 ^ coord (sf i)) m u)) (m * ii + (P.mark + P.bs))
      = if P.sgn (sf ii) then 2 else 0 := by
  have hfit : ∀ k, 2 * (3 ^ coord (sf k) * P.romK) < 3 ^ m :=
    fun k => row_fits hOk hP hS hG (hsf k)
  have hspan : P.mark + P.bs < m := by
    have h := rom_span_lt100 hOk hP hS hG
    have := P.bs_lt
    omega
  rw [romK_mul_history hOk hP hS hG, ← Ternary.dg_row _ ii hspan, row_rowsum hfit u ii hi,
    Ternary.dg_two_mul (P.romK_bool.mul_pow _), P.dg_romK_shift_sgn (hsf ii)]
  split <;> norm_num

/-- The zero-request port carries the zero-request label, row by row. -/
theorem dg_zreq_row {sf : ℕ → ℕ} (hsf : ∀ i, sf i < P.n) {ii : ℕ} (hi : ii < u) :
    Ternary.dg (P.romK * (2 * rowsum (fun i => 3 ^ coord (sf i)) m u)) (m * ii + (P.mark + P.bz))
      = if P.zreq (sf ii) then 2 else 0 := by
  have hfit : ∀ k, 2 * (3 ^ coord (sf k) * P.romK) < 3 ^ m :=
    fun k => row_fits hOk hP hS hG (hsf k)
  have hspan : P.mark + P.bz < m := rom_span_lt100 hOk hP hS hG
  rw [romK_mul_history hOk hP hS hG, ← Ternary.dg_row _ ii hspan, row_rowsum hfit u ii hi,
    Ternary.dg_two_mul (P.romK_bool.mul_pow _), P.dg_romK_shift_zreq (hsf ii)]
  split <;> norm_num

end Transport

end Jones1980
