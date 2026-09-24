import Surreal.Algebra.QuadraticIdealDefinition

/-!
# Quadratic obstructions in an embedded coefficient ring

The nonsquare obstruction and its converse used in `odg:def:rem:numberfieldideal`.
A containing field suffices for root exclusion; it need not be the fraction
field of the coefficient ring. A square in the fraction field instead
supplies a nonzero ordinary solution by clearing denominators.
-/

namespace Surreal.QuadraticIdeal

/-- A nonsquare in any containing field rules out nonzero first coordinates. -/
theorem zero_of_nonsquare_embedding {O K : Type*} [CommRing O] [Field K]
    (i : O →+* K) (hi : Function.Injective i) (δ : O) (hn : ¬IsSquare (i δ))
    (a b : O) (h : a ^ 2 = δ * b ^ 2) : a = 0 := by
  have hb : i b = 0 := by
    by_contra hb
    have he : (i a / i b) ^ 2 = i δ := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hb)]
      simpa only [map_pow, map_mul] using congrArg i h
    exact hn ⟨i a / i b, by simpa only [pow_two] using he.symm⟩
  apply hi
  have he := congrArg i h
  simpa only [map_pow, map_mul, hb, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
    pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0), map_zero] using he

/-- If the nonzero radicand is a square in the fraction field, there is a nonzero ordinary solution. -/
theorem exists_nonzero_quadratic_of_fraction_square {O Q : Type*}
    [CommRing O] [IsDomain O] [Field Q] [Algebra O Q] [IsFractionRing O Q]
    (δ : O) (hd : δ ≠ 0) (hs : IsSquare (algebraMap O Q δ)) :
    ∃ a b : O, a ≠ 0 ∧ a ^ 2 = δ * b ^ 2 := by
  obtain ⟨r, hr⟩ := hs
  obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective O r
  have hb : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbQ : algebraMap O Q b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O Q)).mpr hb
  have hsq : (algebraMap O Q a / algebraMap O Q b) ^ 2 = algebraMap O Q δ := by
    rw [he]
    simpa only [pow_two] using hr.symm
  have hab : a ^ 2 = δ * b ^ 2 := by
    apply IsFractionRing.injective O Q
    rw [map_pow, map_mul, map_pow]
    exact (div_eq_iff (pow_ne_zero 2 hbQ)).mp (by simpa only [div_pow] using hsq)
  refine ⟨a, b, ?_, hab⟩
  intro ha
  rw [ha, zero_pow (by decide)] at hab
  exact (mul_ne_zero hd (pow_ne_zero 2 hb)) hab.symm

end Surreal.QuadraticIdeal
