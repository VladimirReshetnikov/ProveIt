import Diophantine.Common.PellMod

/-!
# Pell recurrences with an arbitrary integer parameter

The Pell sequences `χ_a, ψ_a` of Mathlib (`Pell.xn`, `Pell.yn`) need a natural
parameter `a > 1`.  The doubled-index Pell argument of the 99-operation system
reduces an auxiliary parameter `G` modulo `f` to `−χ_A(2)`, so it needs the
recurrences

* `x_z(0) = 1, x_z(1) = z, x_z(t+2) = 2z x_z(t+1) − x_z(t)`,
* `y_z(0) = 0, y_z(1) = 1, y_z(t+2) = 2z y_z(t+1) − y_z(t)`

for every integer `z`, together with:

* they agree with `χ_a, ψ_a` for a natural parameter `a > 1`;
* they are polynomial in the parameter, so congruent parameters give
  congruent sequences;
* `x_{−z}(t) = (−1)^t x_z(t)`, `y_{−z}(t) = (−1)^(t+1) y_z(t)`;
* `x_1(t) = 1`, `y_1(t) = t`;
* the composition identities `χ_a(2t) = x_{χ_a(2)}(t)` and
  `ψ_a(2t) = ψ_a(2) y_{χ_a(2)}(t)`;
* `x_z(t)` is odd whenever `z` is odd.
-/

namespace Diophantine

open Pell

/-- The first Pell recurrence with integer parameter `z`. -/
def xr (z : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => z
  | (t + 2) => 2 * z * xr z (t + 1) - xr z t

/-- The second Pell recurrence with integer parameter `z`. -/
def yr (z : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (t + 2) => 2 * z * yr z (t + 1) - yr z t

@[simp] theorem xr_zero (z : ℤ) : xr z 0 = 1 := rfl
@[simp] theorem xr_one' (z : ℤ) : xr z 1 = z := rfl
theorem xr_succ_succ (z : ℤ) (t : ℕ) : xr z (t + 2) = 2 * z * xr z (t + 1) - xr z t := rfl
@[simp] theorem yr_zero (z : ℤ) : yr z 0 = 0 := rfl
@[simp] theorem yr_one' (z : ℤ) : yr z 1 = 1 := rfl
theorem yr_succ_succ (z : ℤ) (t : ℕ) : yr z (t + 2) = 2 * z * yr z (t + 1) - yr z t := rfl

/-- Two-step induction helper. -/
theorem two_step {P : ℕ → Prop} (h0 : P 0) (h1 : P 1) (hs : ∀ t, P t → P (t + 1) → P (t + 2)) :
    ∀ t, P t :=
  Nat.twoStepInduction h0 h1 hs

variable {a : ℕ} (a1 : 1 < a)

theorem xn_eq_xr : ∀ t, (xn a1 t : ℤ) = xr a t := by
  refine two_step (by simp) (by simp) ?_
  intro t h1 h2
  have := xn_succ_succ a1 t
  rw [xr_succ_succ, ← h1, ← h2]
  have e : (xn a1 (t + 2) : ℤ) + xn a1 t = 2 * a * xn a1 (t + 1) := by exact_mod_cast this
  linarith

theorem yn_eq_yr : ∀ t, (yn a1 t : ℤ) = yr a t := by
  refine two_step (by simp) (by simp) ?_
  intro t h1 h2
  have := yn_succ_succ a1 t
  rw [yr_succ_succ, ← h1, ← h2]
  have e : (yn a1 (t + 2) : ℤ) + yn a1 t = 2 * a * yn a1 (t + 1) := by exact_mod_cast this
  linarith

theorem xr_modEq {z z' m : ℤ} (h : z ≡ z' [ZMOD m]) : ∀ t, xr z t ≡ xr z' t [ZMOD m] := by
  refine two_step (by simp) (by simpa using h) ?_
  intro t h1 h2
  rw [xr_succ_succ, xr_succ_succ]
  exact Int.ModEq.sub ((Int.ModEq.mul_left 2 h).mul h2) h1

theorem yr_modEq {z z' m : ℤ} (h : z ≡ z' [ZMOD m]) : ∀ t, yr z t ≡ yr z' t [ZMOD m] := by
  refine two_step (by simp) (by simp) ?_
  intro t h1 h2
  rw [yr_succ_succ, yr_succ_succ]
  exact Int.ModEq.sub ((Int.ModEq.mul_left 2 h).mul h2) h1

theorem xr_neg (z : ℤ) : ∀ t, xr (-z) t = (-1) ^ t * xr z t := by
  refine two_step (by simp) (by simp) ?_
  intro t h1 h2
  rw [xr_succ_succ, xr_succ_succ, h1, h2]
  ring

theorem yr_neg (z : ℤ) : ∀ t, yr (-z) t = (-1) ^ (t + 1) * yr z t := by
  refine two_step (by simp) (by simp) ?_
  intro t h1 h2
  rw [yr_succ_succ, yr_succ_succ, h1, h2]
  ring

theorem xr_one : ∀ t, xr 1 t = 1 := by
  refine two_step (by simp) (by simp) ?_
  intro t h1 h2
  rw [xr_succ_succ, h1, h2]; ring

theorem yr_one : ∀ t, yr 1 t = t := by
  refine two_step (by simp) (by simp) ?_
  intro t h1 h2
  rw [yr_succ_succ, h1, h2]; push_cast; ring

/-- The shifted identity `χ_a(m + 2) + χ_a(m − 2) = 2 χ_a(m) χ_a(2)`.
The hypothesis `2 ≤ m` ensures that the natural index `m - 2` is the
ordinary difference, so the Pell subtraction formula applies. -/
theorem xn_add_two_add_sub_two {m : ℕ} (hm : 2 ≤ m) :
    (xn a1 (m + 2) : ℤ) + xn a1 (m - 2) = 2 * xn a1 m * xn a1 2 := by
  have h1 := xn_add a1 m 2
  have h2 := xz_sub a1 hm
  simp only [Pell.xz, Pell.yz] at h2
  have h1' := congrArg (Nat.cast : ℕ → ℤ) h1
  push_cast at h1'
  linarith [h1', h2]

theorem yn_add_two_add_sub_two {m : ℕ} (hm : 2 ≤ m) :
    (yn a1 (m + 2) : ℤ) + yn a1 (m - 2) = 2 * yn a1 m * xn a1 2 := by
  have h1 : (yn a1 (m + 2) : ℤ) = xn a1 m * yn a1 2 + yn a1 m * xn a1 2 := by
    have := yn_add a1 m 2; exact_mod_cast this
  have h2 := yz_sub a1 hm
  simp only [Pell.xz, Pell.yz] at h2
  rw [h1, h2]; ring

/-- `χ_a(2t) = x_{χ_a(2)}(t)`. -/
theorem xn_two_mul_eq_xr : ∀ t, (xn a1 (2 * t) : ℤ) = xr (xn a1 2) t := by
  refine two_step (by simp) (by simp) ?_
  intro t h1 h2
  rw [xr_succ_succ, ← h1, ← h2]
  have e := xn_add_two_add_sub_two a1 (m := 2 * (t + 1)) (by omega)
  have e1 : 2 * (t + 1) + 2 = 2 * (t + 2) := by ring
  have e2 : 2 * (t + 1) - 2 = 2 * t := by omega
  rw [e1, e2] at e
  linarith

/-- `ψ_a(2t) = ψ_a(2) y_{χ_a(2)}(t)`. -/
theorem yn_two_mul_eq_yr : ∀ t, (yn a1 (2 * t) : ℤ) = yn a1 2 * yr (xn a1 2) t := by
  refine two_step (by simp) (by simp) ?_
  intro t h1 h2
  rw [yr_succ_succ]
  have e := yn_add_two_add_sub_two a1 (m := 2 * (t + 1)) (by omega)
  have e1 : 2 * (t + 1) + 2 = 2 * (t + 2) := by ring
  have e2 : 2 * (t + 1) - 2 = 2 * t := by omega
  rw [e1, e2, h1, h2] at e
  linarith

/-- For an odd parameter every `x_z(t)` is odd. -/
theorem xr_odd {z : ℤ} (hz : Odd z) : ∀ t, Odd (xr z t) := by
  refine two_step (by simp) (by simpa using hz) ?_
  intro t h1 h2
  rw [xr_succ_succ]
  obtain ⟨k, hk⟩ := h1
  refine ⟨z * xr z (t + 1) - k - 1, ?_⟩
  rw [hk]; ring

end Diophantine
