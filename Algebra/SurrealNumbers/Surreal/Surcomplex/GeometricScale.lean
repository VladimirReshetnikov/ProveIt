import Surreal.Surcomplex.GeometricSeries

/-!
# The omitted geometric scale

For `t = tMonomial 1`, the error after the powers from zero through `N`
has valuation exactly `N + 1`. Every such finite exponent is below the
actual surreal ordinal omega, so the absolute value, or surcomplex modulus,
of the error exceeds `tMonomial omega`. The ball with that named radius
around `(1 - t)⁻¹` therefore contains no finite partial sum.

These are the named-radius clauses of `a:ex:geometric` and the actual
surreal and surcomplex instances of `found:ex:archimedean`.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

private theorem geometric_scale_infinitesimal :
    IsInfinitesimal (tMonomial (1 : SignSequence.{u})) := by
  rw [isInfinitesimal_iff_valuation_pos, valuation_tMonomial]
  exact WithTop.coe_lt_coe.mpr zero_lt_one

/-- The finite geometric error begins at the next natural-number exponent. -/
theorem valuation_geometric_tMonomial_one_remainder (N : ℕ) :
    valuation ((1 - tMonomial (1 : SignSequence.{u}))⁻¹ -
      ∑ n ∈ Finset.range (N + 1), tMonomial 1 ^ n) =
      ↑((N + 1 : ℕ) : SignSequence.{u}) := by
  have h := valuation_geometric_strongSum_remainder (tMonomial (1 : SignSequence.{u}))
    geometric_scale_infinitesimal N
  rw [geometric_strongSum _ geometric_scale_infinitesimal] at h
  simpa only [valuation_tMonomial, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one] using h

/-- No finite geometric remainder reaches the radius `t^omega`. -/
theorem tMonomial_omega0_lt_abs_geometric_remainder (N : ℕ) :
    tMonomial (ofOrdinal Ordinal.omega0 : SignSequence.{u}) <
      |(1 - tMonomial 1)⁻¹ - ∑ n ∈ Finset.range (N + 1), tMonomial 1 ^ n| := by
  by_contra h
  have hle := valuation_antitone_nonneg (abs_nonneg _) (le_of_not_gt h)
  rw [valuation_abs, valuation_geometric_tMonomial_one_remainder, valuation_tMonomial] at hle
  exact (WithTop.coe_le_coe.mp hle).not_gt (natCast_lt_omega0 (N + 1))

/-- The named absolute-difference ball excludes every finite partial sum. -/
theorem geometric_partialSum_not_mem_omega0_ball (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), tMonomial (1 : SignSequence.{u}) ^ n) ∉
      {y : SignSequence.{u} | |y - (1 - tMonomial 1)⁻¹| <
        tMonomial (ofOrdinal Ordinal.omega0)} := by
  change ¬ |(∑ n ∈ Finset.range (N + 1), tMonomial (1 : SignSequence.{u}) ^ n) -
    (1 - tMonomial 1)⁻¹| < _
  rw [abs_sub_comm]
  exact (tMonomial_omega0_lt_abs_geometric_remainder N).le.not_gt

end

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex

open Foundations

noncomputable section

private theorem geometric_scale_infinitesimal :
    IsInfinitesimal (tMonomial (1 : SignSequence.{u})) := by
  rw [isInfinitesimal_iff_valuation_pos, valuation_tMonomial]
  exact WithTop.coe_lt_coe.mpr zero_lt_one

/-- The complex geometric error has the same next natural-number valuation. -/
theorem valuation_geometric_tMonomial_one_remainder (N : ℕ) :
    valuation ((1 - tMonomial (1 : SignSequence.{u}))⁻¹ -
      ∑ n ∈ Finset.range (N + 1), tMonomial 1 ^ n) =
      ↑((N + 1 : ℕ) : SignSequence.{u}) := by
  have h := valuation_geometric_strongSum_remainder (tMonomial (1 : SignSequence.{u}))
    geometric_scale_infinitesimal N
  rw [geometric_strongSum _ geometric_scale_infinitesimal] at h
  simpa only [valuation_tMonomial, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one] using h

/-- The surcomplex modulus of each finite error strictly exceeds `t^omega`. -/
theorem tMonomial_omega0_lt_modulus_geometric_remainder (N : ℕ) :
    SignSequence.tMonomial (SignSequence.ofOrdinal Ordinal.omega0 : SignSequence.{u}) <
      modulus ((1 - tMonomial 1)⁻¹ - ∑ n ∈ Finset.range (N + 1), tMonomial 1 ^ n) := by
  by_contra h
  have hle := SignSequence.valuation_antitone_nonneg (modulus_nonneg _) (le_of_not_gt h)
  rw [← valuation_eq_modulus, valuation_geometric_tMonomial_one_remainder,
    SignSequence.valuation_tMonomial] at hle
  exact (WithTop.coe_le_coe.mp hle).not_gt (SignSequence.natCast_lt_omega0 (N + 1))

/-- The source's named fine ball contains no finite geometric partial sum. -/
theorem geometric_partialSum_not_mem_omega0_fineBall (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), tMonomial (1 : SignSequence.{u}) ^ n) ∉
      fineBall ((1 - tMonomial 1)⁻¹)
        (SignSequence.tMonomial (SignSequence.ofOrdinal Ordinal.omega0)) := by
  rw [fineBall_eq_modulus _ (SignSequence.tMonomial_pos _)]
  change ¬ modulus ((∑ n ∈ Finset.range (N + 1), tMonomial (1 : SignSequence.{u}) ^ n) -
    (1 - tMonomial 1)⁻¹) < _
  rw [← neg_sub ((1 - tMonomial (1 : SignSequence.{u}))⁻¹), modulus_neg]
  exact (tMonomial_omega0_lt_modulus_geometric_remainder N).le.not_gt

end

end Surreal.Surcomplex
