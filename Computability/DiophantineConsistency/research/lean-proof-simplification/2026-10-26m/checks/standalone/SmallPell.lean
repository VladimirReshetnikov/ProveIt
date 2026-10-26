import Mathlib.NumberTheory.Pell
import Mathlib.Tactic

namespace AdditionalProofSimplifications

/-- A positive Pell solution whose second coordinate is at most three is
automatically fundamental: every nontrivial positive power beyond the first
already has second coordinate at least four. -/
theorem isFundamental_of_y_le_three {d : ℤ} {a : Pell.Solution₁ d}
    (hx : 1 < a.x) (hy : 0 < a.y) (hsmall : a.y ≤ 3) : Pell.IsFundamental a := by
  obtain ⟨f, hf⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (Pell.Solution₁.d_pos_of_one_lt_x hx) (Pell.Solution₁.d_nonsquare_of_one_lt_x hx)
  obtain ⟨n, rfl⟩ := hf.eq_pow_of_nonneg (by omega) hy.le
  have hn : n < 2 := by
    by_contra hn
    have h2 := hf.y_strictMono.monotone (show (2 : ℤ) ≤ n by omega)
    simp only [zpow_natCast, zpow_ofNat, pow_two, Pell.Solution₁.y_mul] at h2
    have hfx := hf.1
    have hfy := hf.2.1
    nlinarith only [h2, hsmall, hfx, hfy, mul_nonneg (show (0 : ℤ) ≤ f.x - 2 by omega)
      (show (0 : ℤ) ≤ f.y - 1 by omega)]
  interval_cases n
  · simp at hy
  · simpa using hf

def firstUnit (Q : ℕ) : Pell.Solution₁ ((Q : ℤ) * (Q + 1)) :=
  Pell.Solution₁.mk (2 * Q + 1) 2 (by ring)

theorem firstUnit_fundamental {Q : ℕ} (hQ : 0 < Q) :
    Pell.IsFundamental (firstUnit Q) := by
  exact isFundamental_of_y_le_three
    (by change (1 : ℤ) < 2 * Q + 1; omega) (by norm_num [firstUnit]) (by norm_num [firstUnit])

/-- The bound three in the generic criterion cannot be increased to four. -/
theorem small_y_bound_sharp :
    ∃ a : Pell.Solution₁ 3, 1 < a.x ∧ a.y = 4 ∧ ¬ Pell.IsFundamental a := by
  refine ⟨Pell.Solution₁.mk 7 4 (by norm_num), by norm_num, rfl, ?_⟩
  intro h
  have hh := h.x_le_x (a := Pell.Solution₁.mk (d := 3) 2 1 (by norm_num)) (by norm_num)
  norm_num at hh

#print axioms isFundamental_of_y_le_three
#print axioms firstUnit_fundamental
#print axioms small_y_bound_sharp

end AdditionalProofSimplifications
