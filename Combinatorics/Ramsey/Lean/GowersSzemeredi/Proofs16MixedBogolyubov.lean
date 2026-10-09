import GowersSzemeredi.Proofs16MixedSpectrum
import GowersSzemeredi.Proofs05Downstream

/-! A mixed Bogolyubov theorem: the common large spectrum controls
(A-A)+(B-B), with an explicit coefficient threshold and Bohr radius. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Frequencies with small phase error control the mixed correlation,
up to twice the Fourier mass of the exceptional frequencies. -/
theorem mixed_weighted_phase_le {N : Nat} [NeZero N]
    (A B S : Finset (ZMod N)) (d : ZMod N)
    (hphase : ∀ r ∈ S, ‖exponential (r * d) - 1‖ ≤ 1 / 2) :
    (∑ r, mixedFourierWeight A B r * ‖exponential (r * d) - 1‖) ≤
      (1 / 2 : Real) * ∑ r, mixedFourierWeight A B r +
        2 * ∑ r ∈ Finset.univ \ S, mixedFourierWeight A B r := by
  have hsplit (f : ZMod N → Real) : (∑ r, f r) =
      (∑ r ∈ S, f r) + ∑ r ∈ Finset.univ \ S, f r := by
    simpa only [Finset.compl_eq_univ_sdiff] using (Finset.sum_add_sum_compl S f).symm
  have hsmall : (∑ r ∈ S, mixedFourierWeight A B r * ‖exponential (r * d) - 1‖) ≤
      (1 / 2 : Real) * ∑ r ∈ S, mixedFourierWeight A B r := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have h := mul_le_mul_of_nonneg_left (hphase r hr) (mixedFourierWeight_nonneg A B r)
    nlinarith only [h]
  have hlarge : (∑ r ∈ Finset.univ \ S, mixedFourierWeight A B r * ‖exponential (r * d) - 1‖) ≤
      2 * ∑ r ∈ Finset.univ \ S, mixedFourierWeight A B r := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have htwo : ‖exponential (r * d) - 1‖ ≤ 2 := by
      have h := norm_sub_le (exponential (r * d)) (1 : Complex)
      rw [show ‖exponential (r * d)‖ = 1 from (ZMod.stdAddChar (N := N)).norm_apply _, norm_one] at h
      norm_num at h ⊢
      exact h
    have h := mul_le_mul_of_nonneg_left htwo (mixedFourierWeight_nonneg A B r)
    nlinarith only [h]
  have htail : 0 ≤ ∑ r ∈ Finset.univ \ S, mixedFourierWeight A B r :=
    Finset.sum_nonneg fun r _ => mixedFourierWeight_nonneg A B r
  rw [hsplit (fun r => mixedFourierWeight A B r * ‖exponential (r * d) - 1‖),
    hsplit (mixedFourierWeight A B)]
  linarith

/-- A small exceptional mass forces a representation by mixed differences. -/
theorem mixed_difference_of_phase_tail {N : Nat} [NeZero N]
    (A B S : Finset (ZMod N)) (d : ZMod N)
    (hphase : ∀ r ∈ S, ‖exponential (r * d) - 1‖ ≤ 1 / 2)
    (htail : 4 * (∑ r ∈ Finset.univ \ S, mixedFourierWeight A B r) <
      (A.card : Real)^2 * (B.card : Real)^2) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B, d = (a₁ - a₂) + (b₁ - b₂) := by
  apply mixedDifferenceCorrelation_representation A B d
  intro hz
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hshift := (mixedDifferenceCorrelation_shift_bound A B d).trans
    (mul_le_mul_of_nonneg_left (mixed_weighted_phase_le A B S d hphase) (by positivity))
  have heq : (N : Real)⁻¹ * ((1 / 2 : Real) * ∑ r, mixedFourierWeight A B r +
      2 * ∑ r ∈ Finset.univ \ S, mixedFourierWeight A B r) =
      (1 / 2 : Real) * ‖mixedDifferenceCorrelation A B 0‖ +
        2 * (∑ r ∈ Finset.univ \ S, mixedFourierWeight A B r) / N := by
    rw [mixedDifferenceCorrelation_zero_norm]
    ring
  rw [heq, hz, zero_sub, norm_neg] at hshift
  have hscaled := mul_le_mul_of_nonneg_right hshift hNR.le
  have hzero := mixedDifferenceCorrelation_zero_lower A B
  have hzero' := (div_le_iff₀ hNR).mp hzero
  field_simp at hscaled
  nlinarith only [hscaled, hzero', htail]

/-- The intersection of large spectra at threshold |A||B|/(4N²)
produces a Bohr neighborhood inside (A-A)+(B-B). -/
theorem mixed_bogolyubov {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (hA : A.Nonempty) (hB : B.Nonempty) (d : ZMod N)
    (hd : d ∈ bohr (commonLargeSpectrum A B ((A.card : Real) * B.card / (4 * (N : Real)^2)))
      (1 / (4 * Real.pi))) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ b₁ ∈ B, ∃ b₂ ∈ B, d = (a₁ - a₂) + (b₁ - b₂) := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hAc : (0 : Real) < A.card := by exact_mod_cast Finset.card_pos.mpr hA
  have hBc : (0 : Real) < B.card := by exact_mod_cast Finset.card_pos.mpr hB
  let tau : Real := (A.card : Real) * B.card / (4 * (N : Real)^2)
  apply mixed_difference_of_phase_tail A B (commonLargeSpectrum A B tau) d
  · intro r hr
    have hcenter := (Finset.mem_filter.mp hd).2 r hr
    have hphase := downstream_norm_exponential_sub_one_le (r * d)
    have hbound : 2 * Real.pi * (centeredAbs (r * d) : Real) / N ≤ 1 / 2 := by
      apply (div_le_iff₀ hNR).mpr
      have h := mul_le_mul_of_nonneg_left hcenter (show 0 ≤ 2 * Real.pi by positivity)
      have heq : 2 * Real.pi * ((1 / (4 * Real.pi)) * (N : Real)) = (1 / 2 : Real) * N := by
        field_simp
        ring
      linarith only [h, heq]
    exact hphase.trans hbound
  · have htau : 0 ≤ tau := by dsimp [tau]; positivity
    have htail := mixedFourierWeight_tail_le_universal A B htau
    have heq : 2 * tau^2 * (N : Real)^4 = (A.card : Real)^2 * (B.card : Real)^2 / 8 := by
      dsimp [tau]
      field_simp
      ring
    rw [heq] at htail
    have hpos : 0 < (A.card : Real)^2 * (B.card : Real)^2 := by positivity
    nlinarith only [htail, hpos]

end LeanProofs.GowersSzemeredi
