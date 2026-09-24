import Surreal.Algebra.PowerSeriesHom

/-!
# Normalized square roots and inverses of formal units

The full `lem:unit-root` in `hahn-evaluation-at-omega`: a series with
constant coefficient one over a characteristic-zero field has a unique
square root with constant coefficient one. The existing unit-square
witness can be normalized by its sign, and the integral-domain identity
for equal squares proves uniqueness. A nonzero constant coefficient also
gives a unique two-sided multiplicative inverse, in arbitrary characteristic.
-/

namespace Surreal.FormalPowerSeries

noncomputable section

/-- The unique square root normalized to have constant coefficient one. -/
theorem existsUnique_sq_of_constantCoeff_one {K : Type*} [Field K] [CharZero K]
    (f : PowerSeries K) (hf : f.constantCoeff = 1) :
    ∃! v : PowerSeries K, v.constantCoeff = 1 ∧ v ^ 2 = f := by
  obtain ⟨v, _, hv⟩ := exists_unit_sq_of_constantCoeff_one f hf
  have hc : v.constantCoeff = 1 ∨ v.constantCoeff = -1 := by
    apply sq_eq_one_iff.mp
    simpa only [map_pow, hf] using congrArg PowerSeries.constantCoeff hv
  have hex : ∃ w : PowerSeries K, w.constantCoeff = 1 ∧ w ^ 2 = f := by
    rcases hc with hc | hc
    · exact ⟨v, hc, hv⟩
    · refine ⟨-v, ?_, ?_⟩
      · simp only [map_neg, hc, neg_neg]
      · simpa only [neg_sq] using hv
  obtain ⟨w, hw⟩ := hex
  refine ⟨w, hw, ?_⟩
  intro z hz
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hz.2.trans hw.2.symm) with h | h
  · exact h
  · have hbad : (1 : K) = -1 := by
      simpa only [map_neg, hz.1, hw.1] using congrArg PowerSeries.constantCoeff h
    norm_num at hbad

/-- Every nonzero constant coefficient gives a unique two-sided formal inverse. -/
theorem existsUnique_inverse_of_constantCoeff_ne_zero {K : Type*} [Field K]
    (f : PowerSeries K) (hf : f.constantCoeff ≠ 0) :
    ∃! g : PowerSeries K, f * g = 1 ∧ g * f = 1 := by
  have hu : IsUnit f :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr hf)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨↑(u⁻¹), by simp, ?_⟩
  intro g hg
  apply u.isUnit.mul_left_cancel
  simpa using hg.1

end

end Surreal.FormalPowerSeries
