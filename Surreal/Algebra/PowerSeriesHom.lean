import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-!
# Restrictions on homomorphisms from formal power series

The kernel dichotomy and necessary infinitesimal condition in
`hahn-evaluation-at-omega`, `prop:kernel` and `thm:necessary`.
The kernel statement works over any coefficient field. The order bound
uses formal square roots of units, with no continuity or strong additivity
assumption on the homomorphism.
-/

namespace Surreal.FormalPowerSeries

noncomputable section

/-- A homomorphism killing the variable factors through the constant coefficient. -/
theorem apply_eq_constantCoeff_of_X_eq_zero {R F : Type*} [CommRing R] [CommRing F]
    (φ : PowerSeries R →+* F) (hX : φ PowerSeries.X = 0) (f : PowerSeries R) :
    φ f = φ (PowerSeries.C f.constantCoeff) := by
  conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const f]
  simp only [map_add, map_mul, hX, zero_mul, zero_add]

/-- Nonzero variable image forces injectivity, independently of summation conventions. -/
theorem injective_of_X_ne_zero {K F : Type*} [Field K] [Field F]
    (φ : PowerSeries K →+* F) (hX : φ PowerSeries.X ≠ 0) : Function.Injective φ := by
  apply (RingHom.injective_iff_ker_eq_bot φ).mpr
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro f hf
  by_contra hne
  have hu := (PowerSeries.isUnit_divided_by_X_pow_order hne).map φ
  have hfactor := congrArg φ (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))
  rw [map_mul, map_pow, hf] at hfactor
  exact (mul_ne_zero (pow_ne_zero _ hX) hu.ne_zero) hfactor

/-- A formal series with constant coefficient one is a square of a unit.
This is the existence clause of `lem:unit-root` in characteristic zero. -/
theorem exists_unit_sq_of_constantCoeff_one {K : Type*} [Field K] [CharZero K]
    (f : PowerSeries K) (hf : f.constantCoeff = 1) :
    ∃ v : PowerSeries K, IsUnit v ∧ v ^ 2 = f := by
  let a := f - 1
  have ha : PowerSeries.HasSubst a := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp [a, hf]
  let E := PowerSeries.substAlgHom (R := K) ha
  let b := PowerSeries.binomialSeries K (1 / 2 : ℚ)
  have hb : b ^ 2 = 1 + PowerSeries.X := by
    rw [pow_two, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa only [Nat.cast_one, pow_one] using PowerSeries.binomialSeries_nat
      (R := ℚ) (A := K) 1
  have hbu : IsUnit b := PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [b])
  refine ⟨E b, hbu.map E.toRingHom, ?_⟩
  rw [← map_pow, hb, map_add, map_one, PowerSeries.substAlgHom_X]
  simp [a]

/-- Every image of a formal series with constant coefficient one is positive
in an ordered field, since its formal square root is a unit. -/
theorem map_pos_of_constantCoeff_one {K F : Type*} [Field K] [CharZero K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (φ : PowerSeries K →+* F) (f : PowerSeries K) (hf : f.constantCoeff = 1) :
    0 < φ f := by
  obtain ⟨v, hv, rfl⟩ := exists_unit_sq_of_constantCoeff_one f hf
  rw [map_pow]
  exact sq_pos_of_ne_zero ((hv.map φ).ne_zero)

/-- The reciprocal-natural bound of `thm:necessary`, over any characteristic-zero
coefficient field and any ordered target field. -/
theorem abs_map_X_lt_one_div {K F : Type*} [Field K] [CharZero K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (φ : PowerSeries K →+* F) (n : ℕ) (hn : 0 < n) :
    |φ PowerSeries.X| < 1 / (n : F) := by
  have hp := map_pos_of_constantCoeff_one φ
    (1 + (n : PowerSeries K) * PowerSeries.X) (by simp)
  have hm := map_pos_of_constantCoeff_one φ
    (1 - (n : PowerSeries K) * PowerSeries.X) (by simp)
  simp only [map_add, map_sub, map_mul, map_one, map_natCast] at hp hm
  rw [abs_lt]
  have hn' : (0 : F) < n := Nat.cast_pos.mpr hn
  constructor
  · apply (neg_lt_iff_pos_add').mpr
    apply (div_pos_iff.mpr (Or.inl ⟨hp, hn'⟩)).trans_eq
    field_simp
  · exact (lt_div_iff₀ hn').mpr (by nlinarith [hm])

/-- An Archimedean ordered target forces the variable image to vanish. -/
theorem map_X_eq_zero_of_archimedean {K F : Type*} [Field K] [CharZero K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Archimedean F]
    (φ : PowerSeries K →+* F) : φ PowerSeries.X = 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (abs_pos.mpr hne)
  have hb := abs_map_X_lt_one_div φ (n + 1) (Nat.succ_pos n)
  exact (not_lt_of_ge hn.le) (by simpa only [Nat.cast_add, Nat.cast_one] using hb)

/-- Thus every such map into an Archimedean field is its constant-term map. -/
theorem apply_eq_constantCoeff_of_archimedean {K F : Type*} [Field K] [CharZero K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F] [Archimedean F]
    (φ : PowerSeries K →+* F) (f : PowerSeries K) :
    φ f = φ (PowerSeries.C f.constantCoeff) :=
  apply_eq_constantCoeff_of_X_eq_zero φ (map_X_eq_zero_of_archimedean φ) f

end
end Surreal.FormalPowerSeries
