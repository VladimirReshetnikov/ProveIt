import Surreal.Foundations.OmnificUnits

/-!
# Omnific divisors of ordinary integers

The full `odg:prop:finitedivisors`. A nonzero integer becomes a unit in the
real support ring. Its omnific divisor is therefore a unit of that ring,
hence finite, and the existing finite-omnific classification applies.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- An omnific divisor of a nonzero ordinary integer is an ordinary integer divisor. -/
theorem omnific_dvd_int_iff (d : OmnificInteger.{u}) (N : ℤ) (hN : N ≠ 0) :
    d ∣ omnificIntCast N ↔ ∃ n : ℤ, d = omnificIntCast n ∧ n ∣ N := by
  constructor
  · rintro ⟨e, he⟩
    have hunit : IsUnit (omnificIntCast N).val := by
      change IsUnit (realConstants (N : ℝ))
      exact (isUnit_iff_ne_zero.mpr (by exact_mod_cast hN)).map realConstants
    have hd : IsUnit d.val := isUnit_of_dvd_unit
      ⟨e.val, congrArg Subtype.val he⟩ hunit
    have hf := nonnegativeSupport_finite_of_isUnit d.val hd
    obtain ⟨n, hn⟩ := (omnific_isFinite_iff d).mp hf
    refine ⟨n, hn, omnificConstantCoeff e, ?_⟩
    have hc := congrArg omnificConstantCoeff he
    simpa only [map_mul, hn, omnificConstantCoeff_intCast] using hc
  · rintro ⟨n, rfl, m, rfl⟩
    exact ⟨omnificIntCast m, map_mul omnificIntCast n m⟩

end
end Surreal.Foundations.SignSequence
