import GowersSzemeredi.Sections01_03
import OAI.Combinatorics.Progressions.Model

/-! Transfer the upstream quantitative density statement to the exact
Gowers headline. The upstream theorem is an explicit premise until its
full proof has been backported and audited in this workspace. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A quadratic lower bound for the exponential gives an elementary,
explicit cutoff at which exponential decay beats the reciprocal. -/
theorem density_exp_lt_inv {C c x : Real} (hC : 0 < C) (hc : 0 < c)
    (hx : 1 ≤ x) (hcut : 4 * C / c ^ 2 ≤ x) :
    C * Real.exp (-c * x) < x⁻¹ := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hcx : 0 < c * x := mul_pos hc hxpos
  have hquad := Real.quadratic_le_exp_of_nonneg hcx.le
  have hcut' : 4 * C ≤ x * c ^ 2 := (div_le_iff₀ (pow_pos hc 2)).mp hcut
  have hprod := mul_le_mul_of_nonneg_right hcut' hxpos.le
  have hCexp : C * x < Real.exp (c * x) := by
    nlinarith only [hprod, hquad, hcx, mul_pos hC hxpos]
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  have h := (lt_div_iff₀ hxpos).mpr hCexp
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- The asymptotic quantitative statement suffices for Theorem 1.3 even
though its constants do not determine Theorem 18.2's fixed threshold. -/
theorem theorem_1_3_of_quantitative_density
    (hquant : OAI.Erdos3.QuantitativeDensityTheorem) : theorem_1_3 := by
  classical
  intro k _hk
  let l := max k 3
  obtain ⟨C, c, eta, hC, hc, heta, hbound⟩ := hquant l (le_max_right _ _)
  let T := max 1 (4 * C / c ^ 2)
  obtain ⟨M, hM⟩ := exists_nat_ge (Real.exp (Real.exp T))
  refine ⟨max 3 M, fun N hN A hA hmass => ?_⟩
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  have hNreal : Real.exp (Real.exp T) ≤ N :=
    hM.trans (by exact_mod_cast (le_max_right 3 M).trans hN)
  have hlog : Real.exp T ≤ Real.log N := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hNreal
  have hT : T ≤ Real.log (Real.log N) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos T) hlog
  let x := Real.log (Real.log N)
  have hx : 1 ≤ x := (le_max_left _ _).trans hT
  have hcut : 4 * C / c ^ 2 ≤ x := (le_max_right _ _).trans hT
  have hpower : x ≤ x ^ (1 + eta) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx
      (show (1 : Real) ≤ 1 + eta by linarith only [heta])
  have hdecay : C * Real.exp (-c * x ^ (1 + eta)) < x⁻¹ := by
    apply lt_of_le_of_lt _ (density_exp_lt_inv hC hc hx hcut)
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hC.le
    nlinarith only [mul_le_mul_of_nonneg_left hpower hc.le]
  have he : theorem_1_3_constant k ≤ 1 := by
    unfold theorem_1_3_constant
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr (by positivity))
  have hi : x⁻¹ ≤ x ^ (-theorem_1_3_constant k) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [he])
  by_contra hfree
  have hfree' : OAI.Erdos3.APFree (A : Set Nat) l := by
    rintro ⟨a, d, hd, hmem⟩
    exact hfree ⟨a, d, hd, fun i hi => hmem i (hi.trans_le (le_max_left _ _))⟩
  have hcard : A.card ≤ OAI.Erdos3.extremalNumber l N :=
    Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hA, hfree'⟩)
  have hlt : (A.card : Real) < N * x ^ (-theorem_1_3_constant k) := by
    calc
      _ ≤ (OAI.Erdos3.extremalNumber l N : Real) := by exact_mod_cast hcard
      _ ≤ C * N * Real.exp (-c * x ^ (1 + eta)) := hbound N hN3
      _ = N * (C * Real.exp (-c * x ^ (1 + eta))) := by ring
      _ < N * x⁻¹ := mul_lt_mul_of_pos_left hdecay hNpos
      _ ≤ _ := mul_le_mul_of_nonneg_left hi hNpos.le
  exact (not_lt_of_ge hmass) hlt

end LeanProofs.GowersSzemeredi
