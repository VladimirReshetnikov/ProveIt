import GowersSzemeredi.Proofs18LengthSixEnvelope
import GowersSzemeredi.Proofs18DensityIterationExponentialBudget
import GowersSzemeredi.Proofs18SzemerediSmallLengths
import GowersSzemeredi.Proofs18QuadraticSourceThreshold

/-! **Theorem 18.2 at length six, from the two recurrence profiles.**

`length_six_function_discrepancy` turns the recurrence profiles in
dimensions one and two into `FunctionDiscrepancyBound 4 α β σ T`. The
preceding modules bound its parameters polynomially or exponentially in
`X = 2/α`:
* `β⁻¹ ≤ X^(2^664)` (`lsBeta_bounds`);
* `σ⁻¹ ≤ exp(X^(2^664+2))` (`lsSigma_inv_le`);
* `T ≤ exp(exp(X^(2^700)))` (`lsThreshold_le`).

At length six, `α = (δ⁶/110592)^32`, so `2^700 ≤ X ≤ δ^(-737)`. The density
iteration (`densityIterationClosedThreshold_le_double_exp_of_exp_budget`)
then gives the closed threshold `≤ exp(exp(X^(2^700+3)))`. That is below
`2^(2^(δ^(-2^711)))`, and so below the source threshold
`2^(2^(δ^(-2^32768)))`.

`theorem_18_2_six_of_profiles` is the result. Its hypotheses are the two
recurrence profiles with constants `K, p ≤ 2^2000`. The explicit constants
of `Proofs16ExplicitConstantBounds` are at most `2^1700`, and the profile
exponent carries a factor `k + 1`. -/
set_option autoImplicit false
set_option exponentiation.threshold 4096
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The uniformity parameter at length six -/

theorem intervalUniformityParameter_six_eq (delta : Real) :
    intervalUniformityParameter delta 6 = (delta ^ 6 / 110592) ^ (32 : Nat) := by
  unfold intervalUniformityParameter
  norm_num

theorem intervalUniformityParameter_six_bounds {delta : Real} (hδ : 0 < delta)
    (hδhalf : delta ≤ 1 / 2) :
    0 < intervalUniformityParameter delta 6 ∧ intervalUniformityParameter delta 6 ≤ delta ∧
      (2 : Real) ^ 700 ≤ 2 / intervalUniformityParameter delta 6 ∧
      2 / intervalUniformityParameter delta 6 ≤ delta⁻¹ ^ (737 : Nat) := by
  rw [intervalUniformityParameter_six_eq]
  have hδ1 : delta ≤ 1 := by linarith only [hδhalf]
  have hu : 2 ≤ delta⁻¹ := by
    rw [← one_div, le_div_iff₀ hδ]; linarith only [hδhalf]
  have hu1 : 1 ≤ delta⁻¹ := le_trans (by norm_num) hu
  set a := delta ^ 6 / 110592 with ha
  have ha0 : 0 < a := by positivity
  have haδ : a ≤ delta ^ 6 := div_le_self (pow_nonneg hδ.le _) (by norm_num)
  have h6 : delta ^ 6 ≤ delta := pow_le_of_le_one hδ.le hδ1 (by norm_num)
  have ha1 : a ≤ 1 := (haδ.trans h6).trans hδ1
  have hainv : a⁻¹ = 110592 * delta⁻¹ ^ 6 := by rw [ha, inv_div, div_eq_mul_inv, inv_pow]
  refine ⟨pow_pos ha0 _, ?_, ?_, ?_⟩
  · calc a ^ (32 : Nat) ≤ a := pow_le_of_le_one ha0.le ha1 (by norm_num)
      _ ≤ delta := haδ.trans h6
  · -- `a⁻¹ ≥ 2^22`
    have h22 : (2 : Real) ^ 22 ≤ a⁻¹ := by
      rw [hainv]
      have : (2 : Real) ^ 6 ≤ delta⁻¹ ^ 6 := pow_le_pow_left₀ (by norm_num) hu 6
      calc (2 : Real) ^ 22 = 2 ^ 16 * 2 ^ 6 := by norm_num
        _ ≤ 110592 * delta⁻¹ ^ 6 := mul_le_mul (by norm_num) this (by norm_num) (by norm_num)
    rw [div_eq_mul_inv, ← inv_pow]
    calc (2 : Real) ^ 700 ≤ 2 * ((2 : Real) ^ 22) ^ 32 := by norm_num
      _ ≤ 2 * (a⁻¹) ^ 32 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h22 32) (by norm_num)
  · have h17 : a⁻¹ ≤ delta⁻¹ ^ 23 := by
      rw [hainv, show (23 : Nat) = 17 + 6 by norm_num, pow_add]
      exact mul_le_mul_of_nonneg_right
        ((show (110592 : Real) ≤ 2 ^ 17 by norm_num).trans (pow_le_pow_left₀ (by norm_num) hu 17))
        (by positivity)
    rw [div_eq_mul_inv, ← inv_pow]
    calc 2 * (a⁻¹) ^ 32 ≤ delta⁻¹ * (delta⁻¹ ^ 23) ^ 32 :=
          mul_le_mul hu (pow_le_pow_left₀ (inv_pos.mpr ha0).le h17 32) (by positivity)
            (le_trans zero_le_one hu1)
      _ = delta⁻¹ ^ (737 : Nat) := by rw [← pow_mul, ← pow_succ']

/-! ### The density iteration -/

/-- The interval-length factor `c = β/(8 bRC(β/64))` has `c⁻¹ ≤ exp(X^(2^670))`. -/
theorem length_factor_inv_le {X beta : Real} (hX : (2 : Real) ^ 700 ≤ X) (hb : 0 < beta)
    (hb1 : beta ≤ 1) (hbi : beta⁻¹ ≤ X ^ ((2 : Nat) ^ 664)) :
    0 < beta / (8 * boundaryRefinementConstant (beta / 64)) ∧
      beta / (8 * boundaryRefinementConstant (beta / 64)) ≤ 1 ∧
      (beta / (8 * boundaryRefinementConstant (beta / 64)))⁻¹ ≤
        Real.exp (X ^ ((2 : Nat) ^ 670)) := by
  have hX2 : 2 ≤ X := le_trans (by norm_num) hX
  have hfixed : section5LocalRefinementConstant 1 1 ≤ X ^ ((2 : Nat) ^ 1082) :=
    (section5_degree_le_three_refinement_constant_upper (by omega)).trans
      (pow_le_pow_left₀ (by norm_num) hX2 _)
  obtain ⟨hc0, hc1, hci⟩ := interval_length_factor_bounds_of_powers hX2 hb hb1 hbi hfixed
  refine ⟨hc0, hc1, ?_⟩
  have hi : (beta / (8 * boundaryRefinementConstant (beta / 64)))⁻¹ ≤ X ^ ((2 : Nat) ^ 1084) :=
    hci.trans (pow_le_pow_right₀ (by linarith only [hX2]) (by norm_num))
  exact (hi.trans (pow_two_pow_le_exp_pow_succ hX2 1084)).trans
    (exp_pow_mono hX2 (by norm_num))

/-- **The closed threshold of the length-six iteration is double exponential.** -/
theorem lengthSixClosedThreshold_le {K1 p1 K2 p2 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    (hK2 : 0 < K2) (hp2 : 0 < p2) {delta : Real} (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2)
    (hK : (K1 : Real) ≤ 2 ^ 2000) (hp : (p1 : Real) ≤ 2 ^ 2000)
    (hK' : (K2 : Real) ≤ 2 ^ 2000) (hp' : (p2 : Real) ≤ 2 ^ 2000) :
    intervalDiscrepancyClosedThreshold 6 delta (lsBeta (intervalUniformityParameter delta 6))
        (lsSigma K1 p1 p2 (intervalUniformityParameter delta 6))
        (lsThreshold K1 p1 K2 p2 (intervalUniformityParameter delta 6)) ≤
      Real.exp (Real.exp ((2 / intervalUniformityParameter delta 6) ^ ((2 : Nat) ^ 700 + 3))) := by
  obtain ⟨ha0, haδ, hXbig, -⟩ := intervalUniformityParameter_six_bounds hδ hδhalf
  set alpha := intervalUniformityParameter delta 6 with halpha
  have ha2 : alpha ≤ 1 / 2 := haδ.trans hδhalf
  have hX2 : 2 ≤ 2 / alpha := le_trans (by norm_num) hXbig
  have hX1 : 1 ≤ 2 / alpha := le_trans (by norm_num) hXbig
  have hX0 : 0 ≤ 2 / alpha := le_trans (by norm_num) hXbig
  have hc3 : ∀ c : Real, c ≤ 2 ^ 2000 → c ≤ (2 / alpha) ^ 3 := fun c hc =>
    hc.trans ((show (2 : Real) ^ 2000 ≤ ((2 : Real) ^ 700) ^ 3 by norm_num).trans
      (pow_le_pow_left₀ (by norm_num) hXbig 3))
  obtain ⟨b0, b1, bi⟩ := lsBeta_bounds ha0 ha2
  obtain ⟨g0, gi⟩ := lsSigma_inv_le hK1 hp1 hp2 ha0 ha2 (hc3 _ hK) (hc3 _ hp) (hc3 _ hp')
  have hT := lsThreshold_le hK1 hp1 hK2 hp2 ha0 ha2 hXbig (hc3 _ hK) (hc3 _ hp) (hc3 _ hK')
    (hc3 _ hp')
  obtain ⟨c0, c1, ci⟩ := length_factor_inv_le hXbig b0 b1 bi
  have hδi : delta⁻¹ ≤ 2 / alpha := by
    rw [div_eq_mul_inv]
    have : delta⁻¹ ≤ alpha⁻¹ := inv_anti₀ ha0 haδ
    linarith only [this, inv_pos.mpr ha0]
  unfold intervalDiscrepancyClosedThreshold
  set beta := lsBeta alpha
  set sigma := lsSigma K1 p1 p2 alpha
  set T := lsThreshold K1 p1 K2 p2 alpha
  set X := 2 / alpha with hX
  clear_value beta sigma T X
  -- the gain `β/8`
  have hgain : (beta / 8)⁻¹ ≤ X ^ ((2 : Nat) ^ 665) := by
    rw [show (beta / 8)⁻¹ = 8 * beta⁻¹ by field_simp, show (2 : Nat) ^ 665 = 3 + ((2 : Nat) ^ 665 - 3)
      by norm_num, pow_add]
    exact mul_le_mul (const_le_pow hX2 (by norm_num)) (bi.trans (pow_le_pow_right₀ hX1 (by norm_num)))
      (inv_pos.mpr b0).le (pow_nonneg hX0 _)
  -- the base `2 max 1 (σ/16)⁻¹`
  have hbase : 2 * max 1 (sigma / 16)⁻¹ ≤ Real.exp (X ^ ((2 : Nat) ^ 665)) := by
    have h16 : (sigma / 16)⁻¹ ≤ Real.exp (X ^ ((2 : Nat) ^ 664 + 3)) := by
      rw [show (sigma / 16)⁻¹ = 16 * sigma⁻¹ by field_simp]
      exact exp_mul_le hX2 (inv_pos.mpr g0).le ((const_le_exp_pow (j := 4) hX2 (by norm_num)).trans
        (exp_pow_mono hX2 (by norm_num))) gi
    have hm : max 1 (sigma / 16)⁻¹ ≤ Real.exp (X ^ ((2 : Nat) ^ 664 + 3)) :=
      max_le (Real.one_le_exp_iff.mpr (pow_nonneg hX0 _)) h16
    exact (exp_mul_le hX2 (le_trans zero_le_one (le_max_left _ _))
      ((const_le_exp_pow (j := 1) hX2 (by norm_num)).trans (exp_pow_mono hX2 (by norm_num))) hm).trans
      (exp_pow_mono hX2 (by norm_num))
  -- the logarithmic budget
  have hstep : max 1 (intervalDiscrepancyStepThreshold 6 delta beta T) ≤
      Real.exp (Real.exp (X ^ ((2 : Nat) ^ 700))) := by
    have hsmall : ∀ x : Real, x ≤ Real.exp (X ^ ((2 : Nat) ^ 700)) →
        x ≤ Real.exp (Real.exp (X ^ ((2 : Nat) ^ 700))) := fun x hx => le_exp_exp_of_le_exp hx
    have h32 : 32 / beta ≤ Real.exp (X ^ ((2 : Nat) ^ 700)) := by
      rw [div_eq_mul_inv]
      exact (exp_mul_le hX2 (inv_pos.mpr b0).le ((const_le_exp_pow (j := 5) hX2 (by norm_num)).trans
        (exp_pow_mono hX2 (by norm_num))) (le_exp_pow_of_le_pow bi)).trans
        (exp_pow_mono hX2 (by norm_num))
    have hden : (512 * ((6 : Nat) : Real) ^ 2 + 1) / delta ^ 6 ≤ Real.exp (X ^ ((2 : Nat) ^ 700)) := by
      rw [div_eq_mul_inv, ← inv_pow]
      have h6 : delta⁻¹ ^ 6 ≤ X ^ 6 := pow_le_pow_left₀ (inv_pos.mpr hδ).le hδi 6
      exact (exp_mul_le (m := 15) hX2 (pow_nonneg (inv_pos.mpr hδ).le _)
        (const_le_exp_pow (j := 15) hX2 (by norm_num))
        ((le_exp_pow_of_le_pow h6).trans (exp_pow_mono hX2 (by norm_num)))).trans
        (exp_pow_mono hX2 (by norm_num))
    unfold intervalDiscrepancyStepThreshold
    apply max_le (hsmall _ (Real.one_le_exp_iff.mpr (pow_nonneg hX0 _)))
    apply max_le (hsmall _ ((const_le_exp_pow (j := 3) hX2 (by norm_num)).trans
      (exp_pow_mono hX2 (by norm_num))))
    exact max_le hT (max_le (hsmall _ h32) (hsmall _ hden))
  have hA : 1 + Real.log (max 1 (intervalDiscrepancyStepThreshold 6 delta beta T)) +
      |Real.log (beta / (8 * boundaryRefinementConstant (beta / 64)))| ≤
      Real.exp (X ^ ((2 : Nat) ^ 700 + 2)) := by
    have hlogT : Real.log (max 1 (intervalDiscrepancyStepThreshold 6 delta beta T)) ≤
        Real.exp (X ^ ((2 : Nat) ^ 700)) :=
      (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr hstep
    have hlogc : |Real.log (beta / (8 * boundaryRefinementConstant (beta / 64)))| ≤
        Real.exp (X ^ ((2 : Nat) ^ 700)) := by
      rw [abs_of_nonpos (Real.log_nonpos c0.le c1), ← Real.log_inv]
      refine ((Real.log_le_iff_le_exp (inv_pos.mpr c0)).mpr ci).trans ?_
      exact (le_exp_pow_of_le_pow (le_refl _)).trans (exp_pow_mono hX2 (by norm_num))
    have h1 : (1 : Real) ≤ Real.exp (X ^ ((2 : Nat) ^ 700)) :=
      Real.one_le_exp_iff.mpr (pow_nonneg hX0 _)
    exact exp_add_le hX2 (exp_add_le hX2 h1 hlogT) (hlogc.trans (exp_pow_mono hX2 (by norm_num)))
  exact densityIterationClosedThreshold_le_double_exp_of_exp_budget _ _ _ _ _
    ((2 : Nat) ^ 665) ((2 : Nat) ^ 665) ((2 : Nat) ^ 700 + 2) (by positivity) hX2 hA hgain hbase
    (by norm_num)

/-! ### The source threshold -/

/-- The length-six closed threshold is below the source's threshold. -/
theorem lengthSixClosedThreshold_le_source {K1 p1 K2 p2 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    (hK2 : 0 < K2) (hp2 : 0 < p2) {delta : Real} (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2)
    (hK : (K1 : Real) ≤ 2 ^ 2000) (hp : (p1 : Real) ≤ 2 ^ 2000)
    (hK' : (K2 : Real) ≤ 2 ^ 2000) (hp' : (p2 : Real) ≤ 2 ^ 2000) :
    intervalDiscrepancyClosedThreshold 6 delta (lsBeta (intervalUniformityParameter delta 6))
        (lsSigma K1 p1 p2 (intervalUniformityParameter delta 6))
        (lsThreshold K1 p1 K2 p2 (intervalUniformityParameter delta 6)) ≤
      szemerediThreshold delta 6 := by
  obtain ⟨ha0, -, hXbig, hXu⟩ := intervalUniformityParameter_six_bounds hδ hδhalf
  refine (lengthSixClosedThreshold_le hK1 hp1 hK2 hp2 hδ hδhalf hK hp hK' hp').trans ?_
  set u : Real := delta⁻¹ with hu'
  have hu : 2 ≤ u := by rw [hu', ← one_div, le_div_iff₀ hδ]; linarith only [hδhalf]
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu
  set q : Nat := 737 * ((2 : Nat) ^ 700 + 3)
  set E : Nat := (2 : Nat) ^ 711
  have hqE : q + 2 ≤ E := by norm_num [q, E]
  have habsorb : (2 / intervalUniformityParameter delta 6) ^ ((2 : Nat) ^ 700 + 3) ≤ u ^ q := by
    have h := pow_le_pow_left₀ (by positivity) hXu ((2 : Nat) ^ 700 + 3)
    simpa only [← pow_mul] using h
  have hexp := exp_exp_pow_le_two_rpow_two_rpow hu hqE
  refine (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr habsorb)).trans (hexp.trans ?_)
  have hsource : (2 : Real) ^ ((2 : Real) ^ (u ^ ((2 : Nat) ^ 32768))) =
      szemerediThreshold delta 6 := by
    unfold szemerediThreshold
    rw [show (2 : Real) ^ (6 + 9 : Nat) = 32768 by norm_num]
    simp only [hu', ← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hsource]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact pow_le_pow_right₀ hu1 (Nat.pow_le_pow_right (by norm_num) (by norm_num))

/-! ### Theorem 18.2 at length six -/

/-- **Theorem 18.2 at length six, from the recurrence profiles in dimensions
one and two** with explicit constants `K, p ≤ 2^2000`. -/
theorem theorem_18_2_six_of_profiles {K1 p1 K2 p2 : Nat} (hK1 : 2 ≤ K1) (hp1 : 0 < p1)
    (hK2 : 2 ≤ K2) (hp2 : 0 < p2)
    (hK1b : (K1 : Real) ≤ 2 ^ 2000) (hp1b : (p1 : Real) ≤ 2 ^ 2000)
    (hK2b : (K2 : Real) ≤ 2 ^ 2000) (hp2b : (p2 : Real) ≤ 2 ^ 2000)
    (hrec1 : Section16RecurrenceProfileWith 1 (familyRecThr 1 K1 p1) (familyRecExp 1 p1))
    (hrec2 : Section16RecurrenceProfileWith 2 (familyRecThr 2 K2 p2) (familyRecExp 2 p2)) :
    Theorem182At 6 := by
  intro delta N hδ hδhalf hN A hA hcard
  obtain ⟨ha0, haδ, -, -⟩ := intervalUniformityParameter_six_bounds hδ hδhalf
  have ha2 : intervalUniformityParameter delta 6 ≤ 1 / 2 := haδ.trans hδhalf
  have hbound : FunctionDiscrepancyBound (6 - 2) (intervalUniformityParameter delta 6)
      (lsBeta (intervalUniformityParameter delta 6))
      (lsSigma K1 p1 p2 (intervalUniformityParameter delta 6))
      (lsThreshold K1 p1 K2 p2 (intervalUniformityParameter delta 6)) :=
    length_six_function_discrepancy hK1 hp1 hrec1 hK2 hp2 hrec2 ha0 ha2
  have hβ := (lsBeta_bounds ha0 ha2).1
  have hX := (intervalUniformityParameter_six_bounds hδ hδhalf).2.2.1
  have hc3 : ∀ c : Real, c ≤ 2 ^ 2000 → c ≤ (2 / intervalUniformityParameter delta 6) ^ 3 :=
    fun c hc => hc.trans ((show (2 : Real) ^ 2000 ≤ ((2 : Real) ^ 700) ^ 3 by norm_num).trans
      (pow_le_pow_left₀ (by norm_num) hX 3))
  have hσ := (lsSigma_inv_le (by omega) hp1 hp2 ha0 ha2 (hc3 _ hK1b) (hc3 _ hp1b) (hc3 _ hp2b)).1
  exact FunctionDiscrepancyBound.natural_szemeredi_closed (k := 6) (by norm_num) hδ hβ hσ hbound N
    ((lengthSixClosedThreshold_le_source (by omega) hp1 (by omega) hp2 hδ hδhalf hK1b hp1b hK2b
      hp2b).trans hN) A hA hcard

/-- **Corollary 18.7 at length six**, from the same recurrence profiles. -/
theorem corollary_18_7_six_of_profiles {K1 p1 K2 p2 : Nat} (hK1 : 2 ≤ K1) (hp1 : 0 < p1)
    (hK2 : 2 ≤ K2) (hp2 : 0 < p2)
    (hK1b : (K1 : Real) ≤ 2 ^ 2000) (hp1b : (p1 : Real) ≤ 2 ^ 2000)
    (hK2b : (K2 : Real) ≤ 2 ^ 2000) (hp2b : (p2 : Real) ≤ 2 ^ 2000)
    (hrec1 : Section16RecurrenceProfileWith 1 (familyRecThr 1 K1 p1) (familyRecExp 1 p1))
    (hrec2 : Section16RecurrenceProfileWith 2 (familyRecThr 2 K2 p2) (familyRecExp 2 p2)) :
    Corollary187At 6 :=
  (theorem_18_2_six_of_profiles hK1 hp1 hK2 hp2 hK1b hp1b hK2b hp2b hrec1 hrec2).corollary_18_7

end LeanProofs.GowersSzemeredi
