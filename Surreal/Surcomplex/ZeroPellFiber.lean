import Surreal.Foundations.OmnificNoGCD
import Surreal.Foundations.OmnificPurelyInfiniteModule

/-!
# The zero Pell fiber over the actual omnific integers

The full `odg:prop:zeropell`: for a positive nonsquare ordinary integer D,
the zero fiber consists exactly of (±√D t, t), with t in the actual purely
infinite omnific ideal. Irrational proportionality forces both constant
coefficients to vanish; the established real module supplies the converse.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Factoring a zero norm in the actual surreal field gives its two real directions. -/
theorem omnific_zero_norm_directions (D : ℤ) (r : ℝ) (hr : r ^ 2 = (D : ℝ))
    (x y : OmnificInteger.{u}) :
    x ^ 2 - omnificIntCast D * y ^ 2 = 0 ↔
      omnificToSurreal x = ofReal r * omnificToSurreal y ∨
        omnificToSurreal x = ofReal (-r) * omnificToSurreal y := by
  have hs : (ofReal r : SignSequence.{u}) ^ 2 = (D : SignSequence.{u}) := by
    rw [← map_pow, hr, map_intCast]
  have he : x ^ 2 - omnificIntCast D * y ^ 2 = 0 ↔
      (omnificToSurreal x) ^ 2 = (ofReal r * omnificToSurreal y) ^ 2 := by
    rw [← omnificToSurreal_injective.eq_iff]
    rw [map_sub, map_mul, map_pow, map_pow, map_zero,
      omnificToSurreal_intCast, sub_eq_zero, mul_pow, hs]
  rw [he, sq_eq_sq_iff_eq_or_eq_neg, map_neg, neg_mul]

/-- An irrational square root parametrizes the zero norm fiber by the purely infinite ideal. -/
theorem omnific_zero_norm_solutions_iff (D : ℤ) (r : ℝ)
    (hr : r ^ 2 = (D : ℝ)) (hirr : Irrational r) (x y : OmnificInteger.{u}) :
    x ^ 2 - omnificIntCast D * y ^ 2 = 0 ↔
      ∃ t : omnificPurelyInfiniteIdeal.{u}, y = t.val ∧
        (x = (r • t).val ∨ x = ((-r) • t).val) := by
  rw [omnific_zero_norm_directions D r hr]
  constructor
  · intro h
    rcases h with h | h
    · have ht := (omnific_irrational_proportional_purelyInfinite r hirr y x h).1
      refine ⟨⟨y, ht⟩, rfl, Or.inl ?_⟩
      apply omnificToSurreal_injective
      exact h
    · have ht := (omnific_irrational_proportional_purelyInfinite (-r) hirr.neg y x h).1
      refine ⟨⟨y, ht⟩, rfl, Or.inr ?_⟩
      apply omnificToSurreal_injective
      exact h
  · rintro ⟨t, rfl, h | h⟩
    · exact Or.inl (by rw [h, omnificPurelyInfinite_real_smul])
    · exact Or.inr (by rw [h, omnificPurelyInfinite_real_smul])

/-- The exact zero Pell fiber for a positive nonsquare ordinary integer. -/
theorem omnific_zero_pell_solutions_iff (D : ℤ) (hD : 0 < D) (hn : ¬ IsSquare D)
    (x y : OmnificInteger.{u}) :
    x ^ 2 - omnificIntCast D * y ^ 2 = 0 ↔
      ∃ t : omnificPurelyInfiniteIdeal.{u}, y = t.val ∧
        (x = (Real.sqrt (D : ℝ) • t).val ∨ x = ((-Real.sqrt (D : ℝ)) • t).val) :=
  omnific_zero_norm_solutions_iff D _ (Real.sq_sqrt (by exact_mod_cast hD.le))
    ((irrational_sqrt_intCast_iff_of_nonneg hD.le).mpr hn) x y

/-- Both coordinates of a zero Pell solution have zero ordinary constant coefficient. -/
theorem omnific_zero_pell_purelyInfinite (D : ℤ) (hD : 0 < D) (hn : ¬ IsSquare D)
    (x y : OmnificInteger.{u}) (h : x ^ 2 - omnificIntCast D * y ^ 2 = 0) :
    x ∈ omnificPurelyInfiniteIdeal ∧ y ∈ omnificPurelyInfiniteIdeal := by
  obtain ⟨t, rfl, hx | hx⟩ := (omnific_zero_pell_solutions_iff D hD hn x y).mp h
  · exact ⟨hx ▸ (Real.sqrt (D : ℝ) • t).property, t.property⟩
  · exact ⟨hx ▸ ((-Real.sqrt (D : ℝ)) • t).property, t.property⟩

/-- Every positive nonsquare parameter has a zero-norm omnific solution with infinite
second coordinate, obtained by taking the purely infinite parameter to be omega. -/
theorem omnific_zero_pell_exists_infinite (D : ℤ) (hD : 0 < D) (hn : ¬ IsSquare D) :
    ∃ x y : OmnificInteger.{u}, x ^ 2 - omnificIntCast D * y ^ 2 = 0 ∧
      ¬ IsFinite (omnificToSurreal y) := by
  let t : omnificPurelyInfiniteIdeal.{u} :=
    ⟨omnificMonomial 1 zero_lt_one, omnificMonomial_mem_purelyInfinite 1 zero_lt_one⟩
  refine ⟨(Real.sqrt (D : ℝ) • t).val, t.val, ?_, ?_⟩
  · exact (omnific_zero_pell_solutions_iff D hD hn _ _).mpr ⟨t, rfl, Or.inl rfl⟩
  · exact omnific_purelyInfinite_not_finite t.val t.property
      (omnificMonomial_ne_zero 1 zero_lt_one)

end
end Surreal.Foundations.SignSequence
