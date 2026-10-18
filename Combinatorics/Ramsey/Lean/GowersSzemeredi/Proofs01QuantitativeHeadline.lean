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
  let L : Real := Real.log (Real.log N)
  have hNpos : (0 : Real) < N := (Real.exp_pos _).trans_le hfloor
  have hlogLower : Real.exp ((2 : Real) ^ e) ≤ Real.log N :=
    (Real.le_log_iff_exp_le hNpos).2 hfloor
  have hlogpos : 0 < Real.log N := (Real.exp_pos _).trans_le hlogLower
  have hLlower : (2 : Real) ^ e ≤ L :=
    (Real.le_log_iff_exp_le hlogpos).2 hlogLower
  have hLpos : 0 < L := (Real.rpow_pos_of_pos (by norm_num) e).trans_le hLlower
  have htwoExp (x : Real) (hx : 0 ≤ x) : (2 : Real) ^ x ≤ Real.exp x := by
    have hbase : (2 : Real) ≤ Real.exp 1 := by
      simpa only [one_add_one_eq_two] using Real.add_one_le_exp 1
    calc
      (2 : Real) ^ x ≤ (Real.exp 1) ^ x :=
        Real.rpow_le_rpow (by norm_num) hbase hx
      _ = Real.exp x := Real.exp_one_rpow x
  change 0 < L ^ (-e⁻¹) ∧ L ^ (-e⁻¹) ≤ 1 / 2 ∧
    (2 : Real) ^ ((2 : Real) ^ ((L ^ (-e⁻¹))⁻¹ ^ e)) ≤ N
  refine ⟨Real.rpow_pos_of_pos hLpos _, ?_, ?_⟩
  · rw [Real.rpow_neg hLpos.le, one_div]
    apply (inv_le_inv₀ (Real.rpow_pos_of_pos hLpos _) (by norm_num : (0 : Real) < 2)).2
    exact (Real.le_rpow_inv_iff_of_pos (by norm_num) hLpos.le he).2 hLlower
  · rw [Real.rpow_neg hLpos.le, inv_inv, Real.rpow_inv_rpow hLpos.le he.ne']
    calc
      (2 : Real) ^ ((2 : Real) ^ L) ≤ Real.exp ((2 : Real) ^ L) :=
        htwoExp _ (Real.rpow_nonneg (by norm_num) _)
      _ ≤ Real.exp (Real.exp L) := Real.exp_le_exp.mpr (htwoExp L hLpos.le)
      _ = (N : Real) := by
        dsimp only [L]
        rw [Real.exp_log hlogpos, Real.exp_log hNpos]

end LeanProofs.GowersSzemeredi
