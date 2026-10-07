import OAI.Combinatorics.Progressions.Estimates.LargeCokernelReciprocalBound
import OAI.Combinatorics.Progressions.Fourier.IntegerBoxCharacterBound

namespace OAI

section

namespace Erdos3

theorem reciprocal_interval_error_absorb (a l C D : ℝ) (ha : 0 < a) (hl : 0 < l)
    (hC : 0 ≤ C) (hscale : a ≤ D * l) :
    C * (1 / a + 1 / l) ≤ C * (1 + D) / a := by
  have h : 1 / l ≤ D / a := by
    apply (div_le_div_iff₀ hl ha).mpr
    simpa using hscale
  calc
    _ ≤ C * (1 / a + D / a) := mul_le_mul_of_nonneg_left (add_le_add le_rfl h) hC
    _ = _ := by ring

theorem boxCokernel_probability_le {I J K : Type*}
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K]
    (e : I → K) (he : Function.Injective e) (lo hi : J → ℤ) (hlen : ∀ j, lo j < hi j)
    (p : ∀ j, FiniteProbabilityWeights (K → Finset.Ico (lo j) (hi j)))
    (B R : ℕ) (hB : 0 < B) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hJ : Fintype.card J = Fintype.card I * (Fintype.card I + 2))
    (hw : ∀ j x, (p j).weight x ≤
      C * (Fintype.card (K → Finset.Ico (lo j) (hi j)) : ℝ)⁻¹)
    (hscale : ∀ j, (R : ℝ) ^ (1 / (Fintype.card I : ℝ)) ≤
      D * ((hi j - lo j : ℤ) : ℝ)) :
    (FiniteProbabilityWeights.pi p).eventProbability
        (largeCokernelEvent (fun _j x i => (x (e i) : ℤ)) B R) ≤
      (C * (1 + D)) ^ Fintype.card J / (B : ℝ) := by
  apply largeCokernel_reciprocal_probability_le p _ B R hB (C * (1 + D))
    (mul_nonneg hC (by positivity)) hJ
  intro a haB haR χ hχ j
  have ha : 0 < a := by omega
  have hχpos : 0 < orderOf χ := by omega
  have h := integerBox_character_probability_le e he (lo j) (hi j) (hlen j)
    (p j) C hC (hw j) χ hχpos
  rw [hχ] at h
  apply h.trans
  apply reciprocal_interval_error_absorb _ _ C D
    (Real.rpow_pos_of_pos (by exact_mod_cast ha) _) (by exact_mod_cast sub_pos.mpr (hlen j)) hC
  exact (Real.rpow_le_rpow (Nat.cast_nonneg a) (by exact_mod_cast haR) (by positivity)).trans
    (hscale j)

end Erdos3

end

end OAI
