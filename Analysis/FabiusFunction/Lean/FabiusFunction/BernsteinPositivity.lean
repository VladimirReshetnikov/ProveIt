import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Piecewise Bernstein certificates for polynomial positivity

The comparative audit records that "no Sturm module exists yet" for
discharging rational positivity checks on an interval
(`ssec:certificate`).  This module supplies the constructive
alternative that certificates in this repository actually use: a
polynomial is nonnegative on `[0,1]` when, on each of `n` equal
subintervals, it is a nonnegative combination of the Bernstein basis
`s^k (1-s)^(d-k)`.  Verifying a concrete certificate needs only
`ring` (the basis identity) and `positivity`/`norm_num` (coefficient
signs) — no root counting, no remainder sequences.

Subdivided Bernstein certificates converge quadratically in the piece
width, so they reach any strict-positivity margin; the `ρ₁` enclosure
(`PerronRootEnclosure`) uses `32` pieces for a margin of order
`10⁻⁷`.

* `nonneg_on_Icc_of_pieces` — positivity on `[0,1]` from the `n`
  per-piece statements, by the explicit cover `t = (i+s)/n`.
* `le_on_Icc_of_pieces` — the same, packaged for a two-sided
  comparison of functions.
-/

set_option autoImplicit false

namespace Fabius

/-- **Piecewise reduction on `[0,1]`**: if `P ((i+s)/n) ≥ 0` for every
piece `i < n` and every `s ∈ [0,1]`, then `P ≥ 0` on `[0,1]`.  The
witness for `t` is the piece `i = min (n-1) ⌊n·t⌋` with offset
`s = n·t - i`. -/
theorem nonneg_on_Icc_of_pieces (P : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (h : ∀ i : ℕ, i < n → ∀ s ∈ Set.Icc (0:ℝ) 1,
      0 ≤ P (((i : ℝ) + s) / n))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : 0 ≤ P t := by
  obtain ⟨ht0, ht1⟩ := ht
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  set i : ℕ := min (n - 1) ⌊n * t⌋₊ with hi
  have hilt : i < n := by
    have : n - 1 < n := Nat.sub_lt hn one_pos
    exact lt_of_le_of_lt (min_le_left _ _) this
  have hnt0 : (0:ℝ) ≤ n * t := mul_nonneg hnR.le ht0
  have hile : (i : ℝ) ≤ n * t := by
    rcases le_or_gt (⌊n * t⌋₊) (n - 1) with hcase | hcase
    · have hieq : i = ⌊n * t⌋₊ := by omega
      rw [hieq]
      exact Nat.floor_le hnt0
    · have hieq : i = n - 1 := by omega
      rw [hieq]
      exact (Nat.cast_le.mpr hcase.le).trans (Nat.floor_le hnt0)
  have hlt : n * t ≤ (i : ℝ) + 1 := by
    rcases le_or_gt (⌊n * t⌋₊) (n - 1) with hcase | hcase
    · have hieq : i = ⌊n * t⌋₊ := by omega
      rw [hieq]
      exact le_of_lt (Nat.lt_floor_add_one _)
    · have hieq : i = n - 1 := by omega
      rw [hieq]
      have h2 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        have h1n : (1:ℕ) ≤ n := hn
        push_cast [Nat.cast_sub h1n]
        ring
      rw [h2]
      calc (n:ℝ) * t ≤ n * 1 := mul_le_mul_of_nonneg_left ht1 hnR.le
        _ = n := mul_one _
  set s : ℝ := n * t - i with hs
  have hs0 : 0 ≤ s := by
    rw [hs]
    linarith
  have hs1 : s ≤ 1 := by
    rw [hs]
    linarith
  have hts : t = ((i : ℝ) + s) / n := by
    rw [eq_div_iff hnR.ne', hs]
    ring
  rw [hts]
  exact h i hilt s ⟨hs0, hs1⟩

/-- **Two-sided piecewise comparison on `[0,1]`**: `f ≤ g` on `[0,1]`
follows from nonnegativity of `g - f` on every piece. -/
theorem le_on_Icc_of_pieces (f g : ℝ → ℝ) (n : ℕ) (hn : 0 < n)
    (h : ∀ i : ℕ, i < n → ∀ s ∈ Set.Icc (0:ℝ) 1,
      0 ≤ g (((i : ℝ) + s) / n) - f (((i : ℝ) + s) / n))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : f t ≤ g t := by
  have := nonneg_on_Icc_of_pieces (fun u => g u - f u) n hn h ht
  linarith [this]

end Fabius
