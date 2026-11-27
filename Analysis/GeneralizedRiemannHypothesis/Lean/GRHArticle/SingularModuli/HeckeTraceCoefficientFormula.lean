import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Trace coefficients for the prime Hecke shifts

Summing the powers of the shifted series selects a single residue class
of coefficients. This allows computing these power sums from one
ordinary integral series before applying Newton's identities.
-/

namespace GRHArticle.SingularModuli

open PowerSeries
open scoped PowerSeries

local notation "χ" => ZMod.stdAddChar

private theorem sum_stdAddChar_mul {p : ℕ} [Fact (Nat.Prime p)] (c : ZMod p) :
    (∑ t : ZMod p, χ (c*t)) = if c = 0 then (p : ℂ) else 0 := by
  classical
  by_cases hc : c = 0
  · simp [hc, ZMod.card]
  · have hχ : (χ : AddChar (ZMod p) ℂ) ≠ 0 := by
      intro h
      have he : χ (1 : ZMod p) = χ (0 : ZMod p) := by rw [h]; simp
      exact one_ne_zero (ZMod.injective_stdAddChar he)
    rw [if_neg hc]
    exact (Equiv.sum_comp (Equiv.mulLeft₀ c hc) (χ : ZMod p → ℂ)).trans
      (AddChar.sum_eq_zero_iff_ne_zero.mpr hχ)

/-- The rescaled trace keeps exactly coefficients whose index is congruent
to the phase exponent modulo the prime. -/
theorem coeff_sum_rescale_stdAddChar (p k n : ℕ) [Fact (Nat.Prime p)] (F : ℂ⟦X⟧) :
    (∑ t : ZMod p, C (χ (-t) ^ k) * rescale (χ t) F).coeff n =
      if (n : ZMod p) = (k : ZMod p) then (p : ℂ) * F.coeff n else 0 := by
  classical
  have hc (t : ZMod p) : χ (-t) ^ k * χ t ^ n = χ (((n : ZMod p) - (k : ZMod p)) * t) := by
    rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [map_sum, coeff_C_mul, coeff_rescale, ← mul_assoc, hc, ← Finset.sum_mul,
    sum_stdAddChar_mul, sub_eq_zero]
  split_ifs <;> simp_all

private theorem heckeShiftPower_eq {p : ℕ} [NeZero p]
    (d k : ℕ) (F : ℂ⟦X⟧) (t : ZMod p) :
    (C (χ (-t)) * X ^ d * rescale (χ t) F) ^ k =
      X ^ (d*k) * (C (χ (-t) ^ k) * rescale (χ t) (F ^ k)) := by
  rw [mul_pow, mul_pow, pow_mul, map_pow, map_pow]
  ring

/-- For each shifted series with initial factor `X^d`, the trace of the
`k`th powers is obtained from `F^k` by keeping one residue class and
shifting the indices by `d*k`. -/
theorem coeff_sum_heckeShift_powers (p d k n : ℕ) [Fact (Nat.Prime p)] (F : ℂ⟦X⟧) :
    (∑ t : ZMod p, (C (χ (-t)) * X ^ d * rescale (χ t) F) ^ k).coeff (n + d*k) =
      if (n : ZMod p) = (k : ZMod p) then (p : ℂ) * (F ^ k).coeff n else 0 := by
  simp only [heckeShiftPower_eq, ← Finset.mul_sum, coeff_X_pow_mul]
  exact coeff_sum_rescale_stdAddChar p k n (F ^ k)

/-- The trace power series in the original `q` variable, expressed using only
integer coefficients of powers of the normalized invariant. -/
noncomputable def heckeTraceSeries (p k : ℕ) (F : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  PowerSeries.mk fun n ↦
    if (p - 1)*k ≤ p*n then (p : ℤ) * (F ^ k).coeff (p*n - (p - 1)*k) else 0

/-- The root-of-unity trace in the (u) variable is the expansion of the
ordinary integer trace series in (q=u^p). -/
theorem sum_heckeShift_powers_eq_expand_trace (p k : ℕ) [hp : Fact (Nat.Prime p)]
    (F : ℤ⟦X⟧) :
    (∑ t : ZMod p, (C (χ (-t)) * X ^ (p-1) *
      rescale (χ t) (PowerSeries.map (Int.castRingHom ℂ) F)) ^ k) =
    expand p hp.out.ne_zero (PowerSeries.map (Int.castRingHom ℂ) (heckeTraceSeries p k F)) := by
  let G := PowerSeries.map (Int.castRingHom ℂ) F
  have hsmall (m : ℕ) (hm : m < (p - 1)*k) :
      (∑ t : ZMod p, (C (χ (-t)) * X ^ (p-1) * rescale (χ t) G) ^ k).coeff m = 0 := by
    simp only [heckeShiftPower_eq, ← Finset.mul_sum, coeff_X_pow_mul', if_neg (not_le.mpr hm)]
  have hresidue (m : ℕ) (hm : (p-1)*k ≤ m) :
      ((m - (p - 1)*k : ℕ) : ZMod p) = (k : ZMod p) ↔ p ∣ m := by
    have hprev : ((p - 1 : ℕ) : ZMod p) = -1 := by
      rw [Nat.cast_sub hp.out.one_lt.le, ZMod.natCast_self, Nat.cast_one, zero_sub]
    rw [Nat.cast_sub hm, Nat.cast_mul, hprev, neg_one_mul, sub_neg_eq_add]
    simp [ZMod.natCast_eq_zero_iff]
  have hlarge (m : ℕ) (hm : (p-1)*k ≤ m) :
      (∑ t : ZMod p, (C (χ (-t)) * X ^ (p-1) * rescale (χ t) G) ^ k).coeff m =
        if p ∣ m then (p : ℂ) * (G ^ k).coeff (m - (p-1)*k) else 0 := by
    have h := coeff_sum_heckeShift_powers p (p-1) k (m - (p-1)*k) G
    rw [Nat.sub_add_cancel hm] at h
    simpa only [hresidue m hm] using h
  ext m
  change (∑ t : ZMod p, (C (χ (-t)) * X ^ (p-1) * rescale (χ t) G) ^ k).coeff m = _
  by_cases hm : (p-1)*k ≤ m
  · rw [hlarge m hm]
    by_cases hd : p ∣ m
    · obtain ⟨n, rfl⟩ := hd
      rw [if_pos (dvd_mul_right p n), coeff_expand_mul, coeff_map, heckeTraceSeries, coeff_mk,
        if_pos hm]
      change (p : ℂ) * ((PowerSeries.map (Int.castRingHom ℂ) F)^k).coeff (p*n-(p-1)*k) =
        (((p : ℤ) * (F^k).coeff (p*n-(p-1)*k) : ℤ) : ℂ)
      rw [Int.cast_mul, Int.cast_natCast, ← map_pow, coeff_map]
      rfl
    · rw [if_neg hd, coeff_expand_of_not_dvd p hp.out.ne_zero _ hd]
  · rw [hsmall _ (lt_of_not_ge hm)]
    by_cases hd : p ∣ m
    · obtain ⟨n, rfl⟩ := hd
      rw [coeff_expand_mul, coeff_map, heckeTraceSeries, coeff_mk, if_neg hm, map_zero]
    · rw [coeff_expand_of_not_dvd p hp.out.ne_zero _ hd]

end GRHArticle.SingularModuli
