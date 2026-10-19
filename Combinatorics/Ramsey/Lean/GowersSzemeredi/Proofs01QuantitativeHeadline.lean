import GowersSzemeredi.Proofs18Consequences

/-!
# The quantitative headline consequence

This module keeps `headline_density_threshold_of_exponent`; the rest of the
development, with its description, is in `Proofs01QuantitativeHeadlineSide`,
outside the final route. -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The log--log density associated to any positive outer exponent reaches
the corresponding double-exponential threshold. -/
theorem headline_density_threshold_of_exponent (e : Real) (he : 0 < e) (N : Nat)
    (hfloor : Real.exp (Real.exp ((2 : Real) ^ e)) ≤ (N : Real)) :
    let L := Real.log (Real.log N)
    let delta := L ^ (-e⁻¹)
    0 < delta ∧ delta ≤ 1 / 2 ∧
      (2 : Real) ^ ((2 : Real) ^ (delta⁻¹ ^ e)) ≤ N := by
  intro L delta
  have hNpos : (0 : Real) < N := (Real.exp_pos _).trans_le hfloor
  have hlog : Real.exp ((2 : Real) ^ e) ≤ Real.log N :=
    (Real.le_log_iff_exp_le hNpos).2 hfloor
  have hlogpos : 0 < Real.log N := (Real.exp_pos _).trans_le hlog
  have hL : (2 : Real) ^ e ≤ L := (Real.le_log_iff_exp_le hlogpos).2 hlog
  have hLpos : 0 < L := (Real.rpow_pos_of_pos two_pos e).trans_le hL
  have hdelta : delta = (L ^ e⁻¹)⁻¹ := Real.rpow_neg hLpos.le _
  have htwo (x : Real) (hx : 0 ≤ x) : (2 : Real) ^ x ≤ Real.exp x :=
    (Real.rpow_le_rpow zero_le_two (by linarith [Real.add_one_le_exp 1]) hx).trans_eq
      (Real.exp_one_rpow x)
  refine ⟨Real.rpow_pos_of_pos hLpos _, ?_, ?_⟩
  · rw [hdelta, one_div]
    exact inv_anti₀ two_pos ((Real.le_rpow_inv_iff_of_pos zero_le_two hLpos.le he).2 hL)
  · rw [hdelta, inv_inv, Real.rpow_inv_rpow hLpos.le he.ne']
    calc (2 : Real) ^ ((2 : Real) ^ L) ≤ Real.exp (Real.exp L) :=
          (htwo _ (by positivity)).trans (Real.exp_le_exp.2 (htwo L hLpos.le))
      _ = N := by rw [show Real.exp L = Real.log N from Real.exp_log hlogpos, Real.exp_log hNpos]

end LeanProofs.GowersSzemeredi
