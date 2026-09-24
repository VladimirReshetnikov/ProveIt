import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Localization.Integral

/-!
# Ordinary integers in principal ideals

Proves `odg:def:lem:intmultiple`. Algebraicity, rather than integrality,
suffices: every nonzero element of any subring of a number field divides
a positive ordinary integer within that subring. For Gaussian integers,
the norm supplies the explicit witness with conjugate quotient.
-/

namespace Surreal.IntegerPrincipalMultiples

noncomputable section

/-- A regular element algebraic over the integers divides a positive ordinary integer. -/
theorem exists_positive_integer_multiple {R : Type*} [CommRing R]
    (a : R) (ha : IsAlgebraic ℤ a) (hreg : a ∈ nonZeroDivisors R) :
    ∃ n : ℤ, 0 < n ∧ a ∣ (n : R) := by
  obtain ⟨n, hn, hd⟩ := ha.exists_nonzero_dvd hreg
  change a ∣ (n : R) at hd
  rcases lt_or_gt_of_ne hn with hn | hn
  · exact ⟨-n, neg_pos.mpr hn, by simpa only [Int.cast_neg] using dvd_neg.mpr hd⟩
  · exact ⟨n, hn, hd⟩

/-- Every nonzero element of a number-field subring divides an ordinary positive integer;
the quotient belongs to the given subring, with no integrality assumption. -/
theorem subring_exists_positive_integer_multiple {K : Type*} [Field K] [NumberField K]
    (o : Subring K) (a : o) (ha : a ≠ 0) :
    ∃ n : ℤ, 0 < n ∧ a ∣ (n : o) := by
  have hK : IsAlgebraic ℤ (a : K) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr
      (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (a : K))
  let f : o →ₐ[ℤ] K :=
    { o.subtype with commutes' := fun n => by simp }
  have ho : IsAlgebraic ℤ a := (isAlgebraic_algHom_iff f Subtype.val_injective).mp hK
  exact exists_positive_integer_multiple a ho (mem_nonZeroDivisors_of_ne_zero ha)

/-- The principal-ideal formulation, using Mathlib's native ideal span. -/
theorem subring_principal_ideal_contains_positive_integer
    {K : Type*} [Field K] [NumberField K] (o : Subring K) (a : o) (ha : a ≠ 0) :
    ∃ n : ℤ, 0 < n ∧ (n : o) ∈ Ideal.span {a} := by
  obtain ⟨n, hn, hd⟩ := subring_exists_positive_integer_multiple o a ha
  exact ⟨n, hn, Ideal.mem_span_singleton.mpr hd⟩

/-- In the Gaussian ring the positive norm is an explicit integer multiple,
and its quotient is the Gaussian conjugate. -/
theorem gaussian_norm_multiple (a : GaussianInt) (ha : a ≠ 0) :
    0 < Zsqrtd.norm a ∧ (Zsqrtd.norm a : GaussianInt) = a * star a :=
  ⟨GaussianInt.norm_pos.mpr ha, Zsqrtd.norm_eq_mul_conj a⟩

/-- The Gaussian norm belongs to the native principal ideal and is positive. -/
theorem gaussian_norm_mem_principal_ideal (a : GaussianInt) (ha : a ≠ 0) :
    0 < Zsqrtd.norm a ∧ (Zsqrtd.norm a : GaussianInt) ∈ Ideal.span {a} :=
  ⟨(gaussian_norm_multiple a ha).1,
    Ideal.mem_span_singleton.mpr ⟨star a, (gaussian_norm_multiple a ha).2⟩⟩

end
end Surreal.IntegerPrincipalMultiples
