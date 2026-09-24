import Surreal.Algebra.PellTwo
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Bounded divisible coordinates in the ordinary Pell sequence

Proves `odg:def:lem:pelldiv` using the native sequence from `odg:eq:pellsequence`.
The recurrence is a permutation of pairs over any commutative ring. Over
Z/mZ its orbit returns to (1, 0) within m² steps, by Mathlib's minimal-period
bound. This includes m = 1 and uses no classification of Pell solutions.
-/

namespace Surreal.PellTwo

noncomputable section

/-- The ordinary recurrence for the first coordinate. -/
theorem X_succ (k : ℕ) : X (k + 1) = 3 * X k + 4 * Y k := by
  simp only [X, Y, pow_succ', Pell.Solution₁.x_mul, fundamental,
    Pell.Solution₁.x_mk, Pell.Solution₁.y_mk]
  ring

/-- The ordinary recurrence for the second coordinate. -/
theorem Y_succ (k : ℕ) : Y (k + 1) = 2 * X k + 3 * Y k := by
  simp only [X, Y, pow_succ', Pell.Solution₁.y_mul, fundamental,
    Pell.Solution₁.x_mk, Pell.Solution₁.y_mk]
  ring

/-- Every positive-index second coordinate is strictly positive. -/
theorem Y_pos {k : ℕ} (hk : 0 < k) : 0 < Y k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact Pell.Solution₁.y_pow_succ_pos (by norm_num [fundamental])
    (by norm_num [fundamental]) n

/-- The recurrence matrix has an integral inverse, including in characteristic 2. -/
def recurrenceEquiv (R : Type*) [CommRing R] : R × R ≃ R × R where
  toFun p := (3 * p.1 + 4 * p.2, 2 * p.1 + 3 * p.2)
  invFun p := (3 * p.1 - 4 * p.2, -2 * p.1 + 3 * p.2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv p := by ext <;> dsimp <;> ring

/-- Iterating the recurrence agrees with coefficient reduction of the native Pell powers. -/
theorem recurrenceEquiv_iterate (R : Type*) [CommRing R] (k : ℕ) :
    (recurrenceEquiv R)^[k] (1, 0) = ((X k : R), (Y k : R)) := by
  induction k with
  | zero => simp [X, Y]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    ext <;> simp [recurrenceEquiv, X_succ, Y_succ]

/-- For every positive modulus, a positive Pell index at most its square gives
first coordinate 1 and second coordinate 0 modulo that modulus. -/
theorem exists_bounded_congruent_one (m : ℕ) (hm : 0 < m) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ^ 2 ∧
      X k ≡ 1 [ZMOD (m : ℤ)] ∧ Y k ≡ 0 [ZMOD (m : ℤ)] ∧ 0 < Y k := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let f := recurrenceEquiv (ZMod m)
  let p : ZMod m × ZMod m := (1, 0)
  let k := Function.minimalPeriod f p
  have hk : 0 < k := Function.minimalPeriod_pos_of_mem_periodicPts
    (f.injective.mem_periodicPts p)
  have hb : k ≤ m ^ 2 := by
    simpa only [Fintype.card_prod, ZMod.card, pow_two] using
      (Function.minimalPeriod_le_card (f := f) (x := p))
  have he : ((X k : ZMod m), (Y k : ZMod m)) = (1, 0) := by
    rw [← recurrenceEquiv_iterate]
    exact Function.isPeriodicPt_minimalPeriod f p
  refine ⟨k, hk, hb, ?_, ?_, Y_pos hk⟩
  · apply (ZMod.intCast_eq_intCast_iff (X k) 1 m).mp
    simpa only [Int.cast_one] using congrArg Prod.fst he
  · apply (ZMod.intCast_eq_intCast_iff (Y k) 0 m).mp
    simpa only [Int.cast_zero] using congrArg Prod.snd he

/-- In particular every positive ordinary integer divides a positive Pell coordinate,
with the same explicit bound on its index. -/
theorem exists_bounded_divisible_coordinate (m : ℕ) (hm : 0 < m) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ^ 2 ∧ (m : ℤ) ∣ Y k ∧ 0 < Y k := by
  obtain ⟨k, hk, hb, _, hy, hp⟩ := exists_bounded_congruent_one m hm
  exact ⟨k, hk, hb, Int.modEq_zero_iff_dvd.mp hy, hp⟩

end
end Surreal.PellTwo
