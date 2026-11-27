import GRHArticle.SingularModuli.CMHeckeInvariance
import GRHArticle.SingularModuli.ModularInvariantPolynomial

/-!
# Polynomial descent for the diagonal of the prime Hecke orbit

The diagonal has pole order `2*p` at infinity. Multiplying by `Δ^(2*p)`
produces a modular form, so the diagonal is a nonzero polynomial in `j`.
-/

namespace GRHArticle.SingularModuli

open Filter Function Polynomial UpperHalfPlane ModularForm ModularFormClass CongruenceSubgroup
open scoped Topology Manifold MatrixGroups ModularForm

local notation "q" => Periodic.qParam 1
local notation "Δ" => ModularForm.discriminant

/-- The prime orbit polynomial evaluated at the invariant of the initial point. -/
noncomputable def analyticPrimeHeckeDiagonal (p : ℕ+) (z : ℍ) : ℂ :=
  (analyticPrimeHeckePolynomial p z).eval (modularInvariant z)

private theorem analyticPrimeHeckeDiagonal_apply (p : ℕ+) (z : ℍ) :
    analyticPrimeHeckeDiagonal p z = (modularInvariant z -
      modularInvariant (heckeScaledPoint p z)) *
      ∏ t ∈ Finset.range (p : ℕ),
        (modularInvariant z - modularInvariant (heckeShiftPoint p t z)) := by
  simp only [analyticPrimeHeckeDiagonal, analyticPrimeHeckePolynomial, eval_mul, eval_prod,
    eval_sub, eval_X, eval_C]

private theorem heckeScaledPoint_tendsto_atImInfty (p : ℕ+) :
    Tendsto (heckeScaledPoint p) atImInfty atImInfty := by
  refine tendsto_comap_iff.mpr ?_
  have h : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  change Tendsto (fun z : ℍ => (heckeScaledPoint p z).im) atImInfty atTop
  simpa [heckeScaledPoint, Complex.mul_im, mul_comm] using h.atTop_mul_const' (show (0 : ℝ) < p by positivity)

private theorem heckeShiftPoint_tendsto_atImInfty (p : ℕ+) (t : ℕ) :
    Tendsto (heckeShiftPoint p t) atImInfty atImInfty := by
  refine tendsto_comap_iff.mpr ?_
  have h : Tendsto UpperHalfPlane.im atImInfty atTop := tendsto_comap
  change Tendsto (fun z : ℍ => (heckeShiftPoint p t z).im) atImInfty atTop
  simpa [heckeShiftPoint, Complex.div_ofReal_im, Complex.add_im, div_eq_mul_inv] using
    h.atTop_mul_const (inv_pos.mpr (show (0 : ℝ) < p by positivity))

private theorem q_heckeScaledPoint (p : ℕ+) (z : ℍ) :
    q (heckeScaledPoint p z) = (q z) ^ (p : ℕ) := by
  simp only [Periodic.qParam, Complex.ofReal_one, div_one, heckeScaledPoint, coe_mk,
    ← Complex.exp_nat_mul, Complex.ofReal_natCast]
  congr 1
  ring

private theorem q_heckeShiftPoint_pow (p : ℕ+) (t : ℕ) (z : ℍ) :
    (q (heckeShiftPoint p t z)) ^ (p : ℕ) = q z := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.pos.ne'
  simp only [Periodic.qParam, Complex.ofReal_one, div_one, heckeShiftPoint, coe_mk,
    ← Complex.exp_nat_mul, Complex.ofReal_natCast]
  rw [show (p : ℂ) * (2 * Real.pi * Complex.I * ((↑z + ↑t) / (p : ℂ))) =
      2 * Real.pi * Complex.I * (z : ℂ) + t * (2 * Real.pi * Complex.I) by
        field_simp [hp],
    Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem tendsto_q_mul_modularInvariant :
    Tendsto (fun z : ℍ => q z * modularInvariant z) atImInfty (𝓝 1) := by
  have h₄ : Tendsto (ModularForm.E₄ : ℍ → ℂ) atImInfty (𝓝 1) := by
    have hper := SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
    have ha := ModularFormClass.analyticAt_cuspFunction_zero
      ModularForm.E₄ one_pos one_mem_strictPeriods_SL
    have h0 := qExpansion_coeff_zero one_pos ha hper
    rw [EisensteinSeries.E_qExpansion_coeff_zero (by decide : 3 ≤ 4) (by decide : Even 4)] at h0
    have hs := ha.continuousAt.tendsto.comp (qParam_tendsto_atImInfty zero_lt_one)
    rw [cuspFunction_apply_zero one_pos ha hper, ← h0] at hs
    exact hs.congr (fun z ↦ eq_cuspFunction z one_ne_zero hper)
  have hη := ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow
  have h := (h₄.pow 3).div hη one_ne_zero
  simp only [one_pow, div_one] at h
  refine h.congr fun z ↦ ?_
  have hq := Periodic.qParam_ne_zero (h := 1) (z : ℂ)
  simp only [modularInvariant, ModularForm.discriminant_eq_q_prod]
  field_simp [hq]
  rfl

private theorem tendsto_pow_q_mul_scaled_difference (p : ℕ+) (hp : 1 < (p : ℕ)) :
    Tendsto (fun z : ℍ => (q z) ^ (p : ℕ) * (modularInvariant z -
      modularInvariant (heckeScaledPoint p z))) atImInfty (𝓝 (-1)) := by
  have h₀ := (qParam_tendsto_atImInfty zero_lt_one).pow ((p : ℕ) - 1)
  have hp₀ : (p : ℕ) - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp
  rw [zero_pow hp₀] at h₀
  have hs := tendsto_q_mul_modularInvariant.comp (heckeScaledPoint_tendsto_atImInfty p)
  have h := (h₀.mul tendsto_q_mul_modularInvariant).sub hs
  simp only [zero_mul, zero_sub] at h
  refine h.congr fun z ↦ ?_
  simp only [Function.comp_apply, q_heckeScaledPoint, mul_sub, ← mul_assoc, ← pow_succ,
    Nat.sub_add_cancel hp.le]

private theorem tendsto_q_mul_shift_difference (p : ℕ+) (hp : 1 < (p : ℕ)) (t : ℕ) :
    Tendsto (fun z : ℍ => q z * (modularInvariant z -
      modularInvariant (heckeShiftPoint p t z))) atImInfty (𝓝 1) := by
  have h₀ := ((qParam_tendsto_atImInfty zero_lt_one).comp
    (heckeShiftPoint_tendsto_atImInfty p t)).pow ((p : ℕ) - 1)
  have hp₀ : (p : ℕ) - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp
  rw [zero_pow hp₀] at h₀
  have hs := tendsto_q_mul_modularInvariant.comp (heckeShiftPoint_tendsto_atImInfty p t)
  have h := tendsto_q_mul_modularInvariant.sub (h₀.mul hs)
  simp only [zero_mul, sub_zero] at h
  refine h.congr fun z ↦ ?_
  simp only [Function.comp_apply, mul_sub, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.le,
    q_heckeShiftPoint_pow]

/-- The normalized Hecke diagonal tends to `-1` at infinity. -/
theorem tendsto_q_pow_mul_analyticPrimeHeckeDiagonal (p : ℕ+) (hp : 1 < (p : ℕ)) :
    Tendsto (fun z : ℍ => (q z) ^ (2 * (p : ℕ)) * analyticPrimeHeckeDiagonal p z)
      atImInfty (𝓝 (-1)) := by
  have hprod := tendsto_finsetProd (Finset.range (p : ℕ))
    (fun t _ ↦ tendsto_q_mul_shift_difference p hp t)
  have h := (tendsto_pow_q_mul_scaled_difference p hp).mul hprod
  simp only [Finset.prod_const_one, mul_one] at h
  refine h.congr fun z ↦ ?_
  simp only [analyticPrimeHeckeDiagonal_apply, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_range, two_mul, pow_add]
  ring

private theorem mdifferentiable_of_coe {f : ℍ → ℍ}
    (hf : MDiff (fun z ↦ (f z : ℂ))) : MDiff f := by
  intro z
  simpa only [Function.comp_def, ofComplex_apply] using
    (mdifferentiableAt_ofComplex (f z).im_pos).comp z (hf z)

private theorem mdifferentiable_analyticPrimeHeckeDiagonal (p : ℕ+) :
    MDiff (analyticPrimeHeckeDiagonal p) := by
  have hj : MDiff modularInvariant := by
    exact (ModularForm.E₄.holo'.pow 3).div CuspForm.discriminant.holo'
      ModularForm.discriminant_ne_zero
  have hscale : MDiff (heckeScaledPoint p) :=
    mdifferentiable_of_coe (mdifferentiable_const.mul mdifferentiable_coe)
  have hshift (t : ℕ) : MDiff (heckeShiftPoint p t) :=
    mdifferentiable_of_coe ((mdifferentiable_coe.add mdifferentiable_const).div
      mdifferentiable_const (fun _ ↦ Complex.ofReal_ne_zero.mpr
        (show (0 : ℝ) < p by positivity).ne'))
  simp only [funext (analyticPrimeHeckeDiagonal_apply p)]
  have hp := MDifferentiable.prod (t := Finset.range (p : ℕ))
    (f := fun t z ↦ modularInvariant z - modularInvariant (heckeShiftPoint p t z))
    (fun t _ ↦ hj.sub (hj.comp (hshift t)))
  have hprod : (∏ t ∈ Finset.range (p : ℕ),
      (fun z : ℍ ↦ modularInvariant z - modularInvariant (heckeShiftPoint p t z))) =
      (fun z : ℍ ↦ ∏ t ∈ Finset.range (p : ℕ),
        (modularInvariant z - modularInvariant (heckeShiftPoint p t z))) := by
    funext z
    exact Finset.prod_apply _ _ _
  rw [hprod] at hp
  exact (hj.sub (hj.comp hscale)).mul hp

private theorem analyticPrimeHeckeDiagonal_smul (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (g : SL(2, ℤ)) (z : ℍ) : analyticPrimeHeckeDiagonal p (g • z) =
      analyticPrimeHeckeDiagonal p z := by
  simp only [analyticPrimeHeckeDiagonal, analyticPrimeHeckePolynomial_smul, modularInvariant_smul]

private noncomputable def regularizedPrimeHeckeDiagonal (p : ℕ+) (z : ℍ) : ℂ :=
  (Δ z) ^ (2 * (p : ℕ)) * analyticPrimeHeckeDiagonal p z

private theorem tendsto_regularizedPrimeHeckeDiagonal (p : ℕ+) [hp : Fact (Nat.Prime (p : ℕ))] :
    Tendsto (regularizedPrimeHeckeDiagonal p) atImInfty (𝓝 (-1)) := by
  have h := (ModularForm.tendsto_atImInfty_tprod_one_sub_eta_q_pow.pow (2 * (p : ℕ))).mul
    (tendsto_q_pow_mul_analyticPrimeHeckeDiagonal p hp.out.one_lt)
  simp only [one_pow, one_mul] at h
  refine h.congr fun z ↦ ?_
  rw [regularizedPrimeHeckeDiagonal, ModularForm.discriminant_eq_q_prod, mul_pow]
  ring

private theorem regularizedPrimeHeckeDiagonal_slash (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (g : SL(2, ℤ)) : regularizedPrimeHeckeDiagonal p ∣[(12 * ((2 * (p : ℕ)) : ℤ))] g =
      regularizedPrimeHeckeDiagonal p := by
  ext z
  rw [SL_slash_apply, regularizedPrimeHeckeDiagonal, analyticPrimeHeckeDiagonal_smul]
  have hd := SlashInvariantForm.slash_action_eqn'' (Γ := 𝒮ℒ) CuspForm.discriminant
      (show (g : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨g, rfl⟩) z
  change Δ (g • z) = denom g z ^ (12 : ℤ) * Δ z at hd
  rw [hd, mul_pow, ← zpow_natCast (denom g z ^ (12 : ℤ)), ← zpow_mul]
  push_cast
  rw [show denom g z ^ (12 * ((2 * (p : ℕ)) : ℤ)) * Δ z ^ (2 * (p : ℕ)) *
      analyticPrimeHeckeDiagonal p z * denom g z ^ (-(12 * ((2 * (p : ℕ)) : ℤ))) =
    (denom g z ^ (12 * ((2 * (p : ℕ)) : ℤ)) *
      denom g z ^ (-(12 * ((2 * (p : ℕ)) : ℤ)))) *
      (Δ z ^ (2 * (p : ℕ)) * analyticPrimeHeckeDiagonal p z) by ring]
  rw [← zpow_add₀ (denom_ne_zero _ z), add_neg_cancel, zpow_zero, one_mul]
  rfl

private noncomputable def regularizedPrimeHeckeModularForm (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    ModularForm 𝒮ℒ (12 * ((2 * (p : ℕ)) : ℤ)) where
  toFun := regularizedPrimeHeckeDiagonal p
  slash_action_eq' := fun _ ⟨g, hg⟩ ↦ hg ▸ regularizedPrimeHeckeDiagonal_slash p g
  holo' := (CuspForm.discriminant.holo'.pow _).mul
    (mdifferentiable_analyticPrimeHeckeDiagonal p)
  bdd_at_cusps' hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro g _
    rw [regularizedPrimeHeckeDiagonal_slash]
    apply isBoundedAtImInfty_iff.mpr
    have hmem : {z : ℍ | regularizedPrimeHeckeDiagonal p z ∈ Metric.ball (-1) 1} ∈
        atImInfty :=
      (tendsto_regularizedPrimeHeckeDiagonal p) (Metric.ball_mem_nhds _ zero_lt_one)
    obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hmem
    refine ⟨2, A, fun z hz ↦ ?_⟩
    have hb := (Metric.mem_ball.mp (hA z hz)).le
    rw [dist_eq_norm] at hb
    calc
      ‖regularizedPrimeHeckeDiagonal p z‖ =
          ‖(regularizedPrimeHeckeDiagonal p z - (-1)) + (-1)‖ := by abel_nf
      _ ≤ ‖regularizedPrimeHeckeDiagonal p z - (-1)‖ + ‖(-1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by
        rw [norm_neg, norm_one]
        linarith only [hb]

/-- The diagonal of the prime Hecke orbit is a nonzero polynomial in the
modular invariant of degree at most `2*p`. -/
theorem exists_poly_analyticPrimeHeckeDiagonal (p : ℕ+) [Fact (Nat.Prime (p : ℕ))] :
    ∃ P : ℂ[X], P ≠ 0 ∧ P.natDegree ≤ 2 * (p : ℕ) ∧
      ∀ z : ℍ, P.eval (modularInvariant z) = analyticPrimeHeckeDiagonal p z := by
  obtain ⟨P, hp, h⟩ := modularForm_weight_twelve_mul_eq_discriminant_pow_polynomial
    (2 * (p : ℕ)) (regularizedPrimeHeckeModularForm p)
  have he (z : ℍ) : P.eval (modularInvariant z) = analyticPrimeHeckeDiagonal p z :=
    mul_left_cancel₀ (pow_ne_zero _ (ModularForm.discriminant_ne_zero z)) (h z).symm
  refine ⟨P, ?_, hp, he⟩
  intro hP
  have heq : regularizedPrimeHeckeDiagonal p = fun _ ↦ 0 := by
    funext z
    rw [regularizedPrimeHeckeDiagonal, ← he, hP, eval_zero, mul_zero]
  have hf := tendsto_regularizedPrimeHeckeDiagonal p
  rw [heq] at hf
  exact (by norm_num : (-1 : ℂ) ≠ 0) (tendsto_nhds_unique hf tendsto_const_nhds)

private theorem tendsto_q_pow_mul_eval_modularInvariant (P : ℂ[X]) (n : ℕ)
    (hn : P.natDegree ≤ n) :
    Tendsto (fun z : ℍ ↦ (q z) ^ n * P.eval (modularInvariant z))
      atImInfty (𝓝 (P.coeff n)) := by
  have hf (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
      Tendsto (fun z : ℍ ↦ (q z) ^ (n - i) * (q z * modularInvariant z) ^ i * P.coeff i)
        atImInfty (𝓝 (if i = n then P.coeff i else 0)) := by
    have h := (((qParam_tendsto_atImInfty zero_lt_one).pow (n - i)).mul
      (tendsto_q_mul_modularInvariant.pow i)).mul_const (P.coeff i)
    by_cases he : i = n
    · subst i
      simpa only [Nat.sub_self, pow_zero, one_pow, one_mul, ite_true] using h
    · have hlt : i < n := lt_of_le_of_ne (by simpa using hi) he
      simpa only [one_pow, mul_one, zero_pow (Nat.sub_ne_zero_of_lt hlt), zero_mul,
        if_neg he] using h
  have hs := tendsto_finsetSum _ hf
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.lt_add_one] at hs
  refine hs.congr fun z ↦ ?_
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hn), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hil : i ≤ n := by simpa using hi
  rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hil]
  ring

/-- The negative of the diagonal of the prime Hecke orbit is monic in the
modular invariant, of degree exactly `2*p`. -/
theorem exists_monic_poly_analyticPrimeHeckeDiagonal (p : ℕ+)
    [hp : Fact (Nat.Prime (p : ℕ))] :
    ∃ P : ℂ[X], P.Monic ∧ P.natDegree = 2 * (p : ℕ) ∧
      ∀ z : ℍ, P.eval (modularInvariant z) = -analyticPrimeHeckeDiagonal p z := by
  obtain ⟨P, _, hP, h⟩ := exists_poly_analyticPrimeHeckeDiagonal p
  have hlimit := tendsto_q_pow_mul_eval_modularInvariant P (2 * (p : ℕ)) hP
  simp_rw [h] at hlimit
  have hc := tendsto_nhds_unique hlimit
    (tendsto_q_pow_mul_analyticPrimeHeckeDiagonal p hp.out.one_lt)
  have hdeg : P.natDegree = 2 * (p : ℕ) :=
    le_antisymm hP (le_natDegree_of_ne_zero (hc.trans_ne (by norm_num)))
  have hmonic : (-P).Monic := by
    change (-P).leadingCoeff = 1
    rw [leadingCoeff_neg, leadingCoeff, hdeg, hc, neg_neg]
  refine ⟨-P, hmonic, ?_, fun z ↦ ?_⟩
  · rw [natDegree_neg, hdeg]
  · rw [eval_neg, h]

end GRHArticle.SingularModuli
