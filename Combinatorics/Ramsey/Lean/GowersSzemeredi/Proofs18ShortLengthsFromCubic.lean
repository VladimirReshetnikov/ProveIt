import GowersSzemeredi.Proofs18SharpInterfaces
import GowersSzemeredi.Proofs18QuadraticSourceThreshold

/-! Short-length instances of the offset-three bound from the existing
quadratic and cubic discrepancy arguments. Lengths two through four use
prefixes of the explicit four-term progression; length five uses the
cubic envelope through the general density iteration. The empty and
one-term cases follow from positive density.

`theorem_18_2_L3_le_five` is in `Proofs18ShortLengthsFromCubicSide`, outside the
final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem szemerediThresholdAt_mono {c c' k : Nat} (hc : c ≤ c') {delta : Real} (hδ : 0 < delta)
    (hδ1 : delta ≤ 1) : szemerediThresholdAt c delta k ≤ szemerediThresholdAt c' delta k := by
  have hu : 1 ≤ delta⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  unfold szemerediThresholdAt
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le hu
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (pow_le_pow_right₀ (by norm_num) (by omega))

/-- A smaller constant gives a stronger Theorem 18.2. -/
theorem Theorem182AtSharp.mono {c c' k : Nat} (h : Theorem182AtSharp c k) (hc : c ≤ c') :
    Theorem182AtSharp c' k := fun delta N hδ hδ2 hN A hA hcard =>
  h delta N hδ hδ2 ((szemerediThresholdAt_mono hc hδ (by linarith)).trans hN) A hA hcard

/-- **Theorem 18.2 with `L + 3` at every length `L ≤ 5`**, from any degree-three base
`EnvBound 3 62` (used at `L = 5`; the shorter lengths need none). -/
theorem theorem_18_2_L3_le_five_of (h3 : EnvBound 3 62) {k : Nat} (hk : k ≤ 5) :
    Theorem182AtSharp 3 k := by
  by_cases hk5 : k = 5
  · subst k
    exact theorem182AtSharp_of_envBound (L := 5) (μ := 62) (c := 3)
      (by norm_num) h3 (by norm_num) (by norm_num) (by norm_num)
  intro delta N hδ hδhalf hN A hA hcard
  by_cases hk1 : k ≤ 1
  · have hN0 : (0 : Real) < N := (Real.rpow_pos_of_pos two_pos _).trans_le hN
    obtain ⟨a, ha⟩ : A.Nonempty :=
      Finset.card_pos.mp (by exact_mod_cast (mul_pos hδ hN0).trans_le hcard)
    exact ⟨a, 1, one_pos, fun i hi => by simpa [show i = 0 by omega] using ha⟩
  have hthreshold : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ 21))) ≤
      szemerediThresholdAt 3 delta k := by
    have h : (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ ((2 : Nat) ^ (2 ^ (k + 3))))) =
        szemerediThresholdAt 3 delta k := by
      unfold szemerediThresholdAt
      simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
    rw [← h]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (Real.rpow_le_rpow_of_exponent_le one_le_two
      (pow_le_pow_right₀ ((one_le_inv₀ hδ).mpr (by linarith)) (Nat.pow_le_pow_right two_pos
        ((show 21 ≤ 2 ^ 5 by norm_num).trans (Nat.pow_le_pow_right two_pos (by omega))))))
  obtain ⟨a, d, hd, hmem⟩ := natural_four_term_explicit_tower delta N hδ hδhalf
    (hthreshold.trans hN) A hA hcard
  exact ⟨a, d, hd, fun i hi => hmem i (by omega)⟩

end LeanProofs.GowersSzemeredi
