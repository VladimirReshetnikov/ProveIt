import GowersSzemeredi.Proofs16BohrDoubling

/-! A regular step between Bohr radii (discrete Bourgain regularity).

With radii `ρ_j = ρ (1 − j/(2m))` from `ρ` down to `ρ/2`, doubling gives
`|B(ρ)| ≤ 4^d |B(ρ/2)|` with `d = |K|`, and the ratio telescopes over `m`
steps. So some step has
`|B(ρ_j)| ≤ 4^(d/m) |B(ρ_{j+1})|`. For `m ≥ d/θ` the factor is about
`1 + θ`, so almost every point of the larger set lies in the smaller.
This lets the packing step of the readout (R) cover all but a small
fraction of a Bohr set by deep points. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Telescoping pigeonhole: if `s 0 ≤ C^m · s m` with `C ≥ 0`, some
consecutive ratio is at most `C`. -/
theorem exists_step_ratio_le {s : Nat → Real} {C : Real} (hC : 0 ≤ C) (m : Nat)
    (hm : 0 < m) (htot : s 0 ≤ C ^ m * s m) :
    ∃ j, j < m ∧ s j ≤ C * s (j + 1) := by
  by_contra hno
  push_neg at hno
  -- then `s 0 > C^j s j` strictly for every `1 ≤ j ≤ m`
  have hgrow : ∀ j, j ≤ m → 0 < j → C ^ j * s j < s 0 := by
    intro j hj hj0
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; simpa using hno 0 hm
      · have h1 := ih (by omega) hpos
        have h2 := hno j (by omega)
        calc C ^ (j + 1) * s (j + 1) = C ^ j * (C * s (j + 1)) := by ring
          _ ≤ C ^ j * s j := mul_le_mul_of_nonneg_left h2.le (pow_nonneg hC j)
          _ < s 0 := h1
  have := hgrow m le_rfl hm
  linarith

/-- **A regular step between Bohr radii.** -/
theorem bohr_exists_regular_step {N : Nat} [NeZero N] (K : Finset (ZMod N)) {ρ : Real} (hρ : 0 < ρ)
    (m : Nat) (hm : 0 < m) :
    ∃ j, j < m ∧
      ((bohr K (ρ * (1 - j / (2 * m)))).card : Real) ≤
        (4 : Real) ^ ((K.card : Real) / m) * (bohr K (ρ * (1 - (j + 1 : Nat) / (2 * m)))).card := by
  set s : Nat → Real := fun j => ((bohr K (ρ * (1 - j / (2 * m)))).card : Real) with hsdef
  have hmR : (0 : Real) < m := by exact_mod_cast hm
  -- doubling between the end radii `ρ` and `ρ/2`
  have hend : s 0 ≤ ((4 : Real) ^ ((K.card : Real) / m)) ^ m * s m := by
    have h4 : ((4 : Real) ^ ((K.card : Real) / m)) ^ m = (4 : Real) ^ K.card := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      rw [div_mul_cancel₀ _ hmR.ne']
      exact Real.rpow_natCast 4 K.card
    rw [h4]
    have hd := bohr_card_le_four_pow K hρ
    simp only [hsdef]
    have e0 : ρ * (1 - ((0 : Nat) : Real) / (2 * m)) = ρ := by simp
    have em : ρ * (1 - (m : Real) / (2 * m)) = ρ / 2 := by field_simp; ring
    rw [e0, em]
    exact_mod_cast hd
  -- apply the telescoping pigeonhole
  exact exists_step_ratio_le (s := s) (C := (4 : Real) ^ ((K.card : Real) / m)) (by positivity) m hm hend

end LeanProofs.GowersSzemeredi
