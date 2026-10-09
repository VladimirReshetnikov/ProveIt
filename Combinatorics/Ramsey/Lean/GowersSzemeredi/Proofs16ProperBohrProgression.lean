import GowersSzemeredi.Proofs05PhaseMetric
import GowersSzemeredi.Proofs16BohrRecentering
import OAI.Combinatorics.Progressions.Fourier.QuarticBohrProgression

/-! Reuse the already-ported proper-progression theorem, converting its
chord-radius convention to the centered phase convention used here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The two character conventions agree exactly. -/
theorem oai_character_eq_exponential {N : Nat} [NeZero N] (r x : ZMod N) :
    OAI.Erdos3.CyclicBohr.character r x = exponential (r * x) := by
  obtain ⟨r, rfl⟩ := ZMod.intCast_surjective r
  obtain ⟨x, rfl⟩ := ZMod.intCast_surjective x
  change (↑(AddChar.zmod N (r : ZMod N) (x : ZMod N)) : Complex) = _
  rw [AddChar.zmod_intCast]
  change _ = ZMod.stdAddChar ((r : ZMod N) * (x : ZMod N))
  conv_rhs => rw [← Int.cast_mul]
  rw [ZMod.stdAddChar_coe]
  simp only [Circle.coe_exp]
  congr 1
  push_cast
  ring

/-- A chord-radius Bohr set lies inside the quarter-radius phase Bohr set. -/
theorem oai_bohr_subset_centered {N : Nat} [NeZero N] (B : OAI.Erdos3.CyclicBohr.Set N) :
    B.carrier ⊆ bohr B.frequencies (B.radius / 4) := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
  have hb := (OAI.Erdos3.CyclicBohr.Set.mem_carrier.mp hx) r hr
  rw [oai_character_eq_exponential, norm_sub_rev] at hb
  have hp := (four_centeredAbs_div_le_phase_norm (r * x)).trans hb
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hmul := (div_le_iff₀ hN).mp hp
  linarith

/-- An explicit large proper progression with room for fourfold sums.
All required upstream files were already in the selected density port. -/
theorem exists_proper_progression_in_bohr {N : Nat} [NeZero N]
    (T : Finset (ZMod N)) {rho w : Real} (hrho : 0 < rho)
    (hw : 0 ≤ w) (hwidth : Real.exp (-w) ≤ rho) :
    ∃ Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N,
      Q.rank ≤ T.card + 1 ∧ Q.Proper ∧ Q.carrier ⊆ bohr T (rho / 4) ∧
      Real.exp (-(((T.card : Real) + 1) * w + 10 * ((T.card : Real) + 1)^2)) * N ≤
        (Q.carrier.card : Real) := by
  let B : OAI.Erdos3.CyclicBohr.Set N := ⟨T, min 1 rho, le_min (by norm_num) hrho.le⟩
  have hBpos : 0 < B.radius := lt_min (by norm_num) hrho
  have hBwidth : Real.exp (-w) ≤ B.radius :=
    le_min (Real.exp_le_one_iff.mpr (by linarith)) hwidth
  obtain ⟨Q, hQrank, hQproper, hQsub, hQcard⟩ :=
    OAI.Erdos3.BohrProgression.exists_large_proper_progression_all B hBpos
      (min_le_left _ _) hw hBwidth
  refine ⟨Q, hQrank, hQproper, ?_, hQcard⟩
  exact hQsub.trans ((oai_bohr_subset_centered B).trans
    (bohr_mono_radius T (div_le_div_of_nonneg_right (min_le_right 1 rho) (by norm_num))))

/-- An explicit logarithmic width works for every positive radius. -/
theorem logarithmic_bohr_width {rho : Real} (hrho : 0 < rho) :
    0 ≤ Real.log (1 + rho⁻¹) ∧ Real.exp (-Real.log (1 + rho⁻¹)) ≤ rho := by
  have hp : 0 < 1 + rho⁻¹ := by positivity
  refine ⟨Real.log_nonneg (by have := inv_nonneg.mpr hrho.le; linarith), ?_⟩
  rw [Real.exp_neg, Real.exp_log hp]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ hp).mpr
  have heq : rho * (1 + rho⁻¹) = rho + 1 := by rw [mul_add, mul_one, mul_inv_cancel₀ hrho.ne']
  rw [heq]
  linarith

/-- The centered progression contains its origin. -/
theorem centered_progression_zero_mem {N : Nat}
    (Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) : (0 : ZMod N) ∈ Q.carrier := by
  refine Finset.mem_image.mpr ⟨(fun i => ⟨Q.radius i, by omega⟩), Finset.mem_univ _, ?_⟩
  simp [OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval,
    OAI.Erdos3.BohrProgression.CyclicCenteredGAP.coeff]

/-- Negation preserves the centered progression. -/
theorem centered_progression_neg_mem {N : Nat}
    (Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) {x : ZMod N}
    (hx : x ∈ Q.carrier) : -x ∈ Q.carrier := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
  let q : Q.Param := fun i => ⟨2 * Q.radius i - (p i).val, by omega⟩
  have hc (i : Fin Q.rank) : Q.coeff q i = -Q.coeff p i := by
    dsimp [OAI.Erdos3.BohrProgression.CyclicCenteredGAP.coeff, q]
    have hi := (p i).isLt
    omega
  refine Finset.mem_image.mpr ⟨q, Finset.mem_univ _, ?_⟩
  simp only [OAI.Erdos3.BohrProgression.CyclicCenteredGAP.eval, hc,
    Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

end LeanProofs.GowersSzemeredi
