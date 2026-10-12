import GowersSzemeredi.Proofs18GenericEnvelopeStep
import GowersSzemeredi.Proofs18DensityIterationExponentialBudget
import GowersSzemeredi.Proofs18GeneralIteration
import GowersSzemeredi.Proofs18SingleLengthStatements

/-! Theorem 18.2 at length `L` from a degree-`(L−2)` envelope
(Notes L.7a, F4).

* `intervalUniformityParameter_gen_bounds`: `α ≤ δ` and
  `2/α ≤ (δ⁻¹)^(2^(2L+4))`.
* `closedThreshold_le_of_env`: the closed threshold of the density
  iteration is at most `exp(exp(X^(2^(μ+9))))` when the degree-`(L−2)` bound
  has envelope `μ`.
* `theorem182At_of_envBound`: `EnvBound (L−2) μ` gives `Theorem182At L`
  once `μ + 2L + 14 ≤ 2^(L+9)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-! ### The uniformity parameter -/

theorem interval_exponent_le (L : Nat) : 1 + (4 * L + 9) * 2 ^ (L - 1) ≤ 2 ^ (2 * L + 4) := by
  rcases Nat.eq_zero_or_pos L with h0 | hpos
  · subst h0; norm_num
  have hL : L < 2 ^ L := Nat.lt_two_pow_self
  have h1 : 4 * L + 9 ≤ 2 ^ (L + 4) := by
    have : 2 ^ (L + 4) = 16 * 2 ^ L := by rw [pow_add]; ring
    have := Nat.one_le_two_pow (n := L)
    omega
  have h5 : 2 ^ (L - 1) * 2 = 2 ^ L := by
    rw [← pow_succ]; congr 1; omega
  have h7 : 2 ^ (L + 4) * 2 ^ L = 2 ^ (2 * L + 4) := by rw [← pow_add]; ring_nf
  have h6 : (4 * L + 9) * 2 ^ (L - 1) * 2 ≤ 2 ^ (2 * L + 4) := by
    rw [mul_assoc, h5, ← h7]; exact Nat.mul_le_mul_right _ h1
  have hX1 : 1 ≤ (4 * L + 9) * 2 ^ (L - 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))
  generalize (4 * L + 9) * 2 ^ (L - 1) = X at h6 hX1 ⊢
  omega

theorem intervalUniformityParameter_gen_bounds {delta : Real} {L : Nat} (hL : 1 ≤ L)
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) :
    0 < intervalUniformityParameter delta L ∧ intervalUniformityParameter delta L ≤ delta ∧
      (2 : Real) ^ L ≤ 2 / intervalUniformityParameter delta L ∧
      2 / intervalUniformityParameter delta L ≤ delta⁻¹ ^ (2 ^ (2 * L + 4)) := by
  have hδ1 : delta ≤ 1 := by linarith
  have hu : 2 ≤ delta⁻¹ := by rw [← one_div, le_div_iff₀ hδ]; linarith
  have hu1 : 1 ≤ delta⁻¹ := le_trans (by norm_num) hu
  unfold intervalUniformityParameter
  set b := delta ^ L / (512 * (L : Real) ^ 3) with hb
  have hL1 : (1 : Real) ≤ L := by exact_mod_cast hL
  have hden : (512 : Real) ≤ 512 * (L : Real) ^ 3 := by
    have : (1 : Real) ≤ (L : Real) ^ 3 := one_le_pow₀ hL1
    linarith
  have hb0 : 0 < b := by positivity
  have hδL : delta ^ L ≤ delta := pow_le_of_le_one hδ.le hδ1 (by omega)
  have hbδ : b ≤ delta ^ L / 512 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
  have hb1 : b ≤ 1 := by
    have : delta ^ L / 512 ≤ 1 := by
      rw [div_le_one (by norm_num)]; linarith [pow_le_one₀ hδ.le hδ1 (n := L)]
    linarith
  have hexp1 : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
  refine ⟨pow_pos hb0 _, ?_, ?_, ?_⟩
  · calc b ^ (2 ^ (L - 1)) ≤ b := pow_le_of_le_one hb0.le hb1 (by omega)
      _ ≤ delta ^ L / 512 := hbδ
      _ ≤ delta := by linarith [hδL]
  · -- `2/α ≥ 2/b ≥ 2^L`
    have hα : b ^ (2 ^ (L - 1)) ≤ b := pow_le_of_le_one hb0.le hb1 (by omega)
    have hb2 : b ≤ ((2 : Real) ^ L)⁻¹ := by
      have h1 : delta ^ L ≤ (1 / 2) ^ L := pow_le_pow_left₀ hδ.le hδhalf L
      have h2 : delta ^ L / 512 ≤ delta ^ L := div_le_self (by positivity) (by norm_num)
      calc b ≤ delta ^ L := hbδ.trans h2
        _ ≤ (1 / 2) ^ L := h1
        _ = ((2 : Real) ^ L)⁻¹ := by rw [one_div, inv_pow]
    rw [le_div_iff₀ (pow_pos hb0 _)]
    calc (2 : Real) ^ L * b ^ (2 ^ (L - 1)) ≤ 2 ^ L * ((2 : Real) ^ L)⁻¹ :=
          mul_le_mul_of_nonneg_left (hα.trans hb2) (by positivity)
      _ = 1 := by field_simp
      _ ≤ 2 := by norm_num
  · -- `b⁻¹ = 512 L³ u^L ≤ u^(4L+9)`
    have hbi : b⁻¹ ≤ delta⁻¹ ^ (4 * L + 9) := by
      rw [hb, inv_div, div_eq_mul_inv, ← inv_pow]
      have h512 : (512 : Real) ≤ delta⁻¹ ^ 9 :=
        (show (512 : Real) = 2 ^ 9 by norm_num) ▸ pow_le_pow_left₀ (by norm_num) hu 9
      have hL3 : (L : Real) ^ 3 ≤ delta⁻¹ ^ (3 * L) := by
        have hL2 : (L : Real) ≤ 2 ^ L := by exact_mod_cast Nat.lt_two_pow_self.le
        calc (L : Real) ^ 3 ≤ ((2 : Real) ^ L) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hL2 3
          _ ≤ (delta⁻¹ ^ L) ^ 3 := pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hu L) 3
          _ = delta⁻¹ ^ (3 * L) := by rw [← pow_mul]; ring_nf
      calc 512 * (L : Real) ^ 3 * delta⁻¹ ^ L ≤ delta⁻¹ ^ 9 * delta⁻¹ ^ (3 * L) * delta⁻¹ ^ L :=
            mul_le_mul_of_nonneg_right (mul_le_mul h512 hL3 (by positivity) (by positivity))
              (by positivity)
        _ = delta⁻¹ ^ (4 * L + 9) := by rw [← pow_add, ← pow_add]; ring_nf
    rw [div_eq_mul_inv, ← inv_pow]
    calc 2 * (b⁻¹) ^ (2 ^ (L - 1)) ≤ delta⁻¹ * (delta⁻¹ ^ (4 * L + 9)) ^ (2 ^ (L - 1)) :=
          mul_le_mul hu (pow_le_pow_left₀ (inv_pos.mpr hb0).le hbi _) (by positivity) (by positivity)
      _ = delta⁻¹ ^ (1 + (4 * L + 9) * 2 ^ (L - 1)) := by rw [← pow_mul, ← pow_succ']; ring_nf
      _ ≤ delta⁻¹ ^ (2 ^ (2 * L + 4)) := pow_le_pow_right₀ hu1 (interval_exponent_le L)

/-! ### The closed threshold -/

/-- **The closed threshold of the density iteration**, from an envelope `μ`. -/
theorem closedThreshold_le_of_env {L μ : Nat} (hL : 1 ≤ L) {delta beta sigma T : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) (hμ : 42 ≤ μ) (hLμ : 4 * L + 20 ≤ 2 ^ μ)
    (b0 : 0 < beta) (b1 : beta ≤ 1) (s0 : 0 < sigma)
    (bi : beta⁻¹ ≤ (2 / intervalUniformityParameter delta L) ^ (2 ^ μ))
    (si : sigma⁻¹ ≤ Real.exp ((2 / intervalUniformityParameter delta L) ^ (2 ^ μ)))
    (Ti : T ≤ Real.exp (Real.exp ((2 / intervalUniformityParameter delta L) ^ (2 ^ μ)))) :
    intervalDiscrepancyClosedThreshold L delta beta sigma T ≤
      Real.exp (Real.exp ((2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)))) := by
  obtain ⟨ha0, haδ, h2L, -⟩ := intervalUniformityParameter_gen_bounds hL hδ hδhalf
  set alpha := intervalUniformityParameter delta L with halpha
  set X := 2 / alpha with hXdef
  have hX : 2 ≤ X := by
    have : (2 : Real) ≤ 2 ^ L := by
      calc (2 : Real) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ L := pow_le_pow_right₀ (by norm_num) hL
    linarith
  have hX0 : (0 : Real) ≤ X := by linarith
  have hX1 : (1 : Real) ≤ X := by linarith
  have hδi : delta⁻¹ ≤ X := by
    rw [hXdef, div_eq_mul_inv]
    have : delta⁻¹ ≤ alpha⁻¹ := inv_anti₀ ha0 haδ
    linarith [inv_pos.mpr ha0]
  have hLX : (L : Real) ≤ X := by
    have : (L : Real) ≤ 2 ^ L := by exact_mod_cast Nat.lt_two_pow_self.le
    linarith
  have hμ2 : 2 ≤ μ := by omega
  have hsmall : ∀ c : Real, ∀ j : Nat, c ≤ 2 ^ (2 ^ j) → j ≤ μ → c ≤ X ^ (2 ^ μ) :=
    fun c j hc hj => pw_mono hX (pw_const hX hc) hj
  -- the gain `β/8`
  have hgain : (beta / 8)⁻¹ ≤ X ^ (2 ^ (μ + 2)) := by
    rw [show (beta / 8)⁻¹ = 8 * beta⁻¹ by field_simp]
    have h8 := hsmall 8 2 (by norm_num) hμ2
    exact (pw_mul hX (by norm_num) (inv_pos.mpr b0).le h8 bi).trans (pw_mono hX le_rfl (by omega))
  -- the base `2 max 1 (σ/16)⁻¹`
  have hbase : 2 * max 1 (sigma / 16)⁻¹ ≤ Real.exp (X ^ (2 ^ (μ + 2))) := by
    have h16 : (sigma / 16)⁻¹ ≤ Real.exp (X ^ (2 ^ (μ + 1))) := by
      rw [show (sigma / 16)⁻¹ = 16 * sigma⁻¹ by field_simp]
      exact ex_mul hX (inv_pos.mpr s0).le (ex_of_pw (hsmall 16 2 (by norm_num) hμ2)) si
    have hm : max 1 (sigma / 16)⁻¹ ≤ Real.exp (X ^ (2 ^ (μ + 1))) :=
      max_le (Real.one_le_exp (by positivity)) h16
    exact ex_mul hX (le_trans zero_le_one (le_max_left _ _))
      (ex_of_pw (hsmall 2 0 (by norm_num) (by omega) |>.trans (pw_mono hX le_rfl (by omega)))) hm
  -- the step threshold
  have hstep : max 1 (intervalDiscrepancyStepThreshold L delta beta T) ≤
      Real.exp (Real.exp (X ^ (2 ^ (μ + 2)))) := by
    have hdex : ∀ x : Real, x ≤ X ^ (2 ^ (μ + 2)) → x ≤ Real.exp (Real.exp (X ^ (2 ^ (μ + 2)))) :=
      fun x hx => le_exp_exp_of_le_exp (ex_of_pw hx)
    have h32 : 32 / beta ≤ X ^ (2 ^ (μ + 2)) := by
      rw [div_eq_mul_inv]
      exact (pw_mul hX (by norm_num) (inv_pos.mpr b0).le (hsmall 32 3 (by norm_num) (by omega)) bi).trans
        (pw_mono hX le_rfl (by omega))
    have hden : (512 * (L : Real) ^ 2 + 1) / delta ^ L ≤ X ^ (2 ^ (μ + 2)) := by
      rw [div_eq_mul_inv, ← inv_pow]
      have hc : 512 * (L : Real) ^ 2 + 1 ≤ X ^ (2 ^ μ) := by
        have h1 : 512 * (L : Real) ^ 2 + 1 ≤ 513 * X ^ 2 := by
          have : (L : Real) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hLX 2
          have : (1 : Real) ≤ X ^ 2 := one_le_pow₀ hX1
          linarith
        have h2 : (513 : Real) * X ^ 2 ≤ X ^ 10 * X ^ 2 :=
          mul_le_mul_of_nonneg_right ((show (513 : Real) ≤ 2 ^ 10 by norm_num).trans
            (pow_le_pow_left₀ (by norm_num) hX 10)) (by positivity)
        refine h1.trans (h2.trans ?_)
        rw [← pow_add]
        exact pw_natpow hX (by
          have : 2 ^ 4 ≤ 2 ^ μ := Nat.pow_le_pow_right (by norm_num) (by omega)
          norm_num at this ⊢; omega)
      have hu : delta⁻¹ ^ L ≤ X ^ (2 ^ μ) :=
        (pow_le_pow_left₀ (inv_pos.mpr hδ).le hδi L).trans (pw_natpow hX (by omega))
      exact (pw_mul hX (by positivity) (by positivity) hc hu).trans (pw_mono hX le_rfl (by omega))
    unfold intervalDiscrepancyStepThreshold
    apply max_le (Real.one_le_exp (by positivity))
    apply max_le (hdex _ (hLX.trans (pw_X hX _)))
    refine max_le (dex_mono hX Ti (by omega)) (max_le (hdex _ h32) (hdex _ hden))
  -- the length factor `c`
  have hC4 : 4 ≤ boundaryRefinementConstant (beta / 64) := section5LocalRefinementConstant_ge_four _ _
  have hCpos : 0 < boundaryRefinementConstant (beta / 64) := lt_of_lt_of_le (by norm_num) hC4
  have hc0 : 0 < beta / (8 * boundaryRefinementConstant (beta / 64)) := by positivity
  have hc1 : beta / (8 * boundaryRefinementConstant (beta / 64)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hBRC : boundaryRefinementConstant (beta / 64) ≤ X ^ (2 ^ (μ + 6)) := by
    have heta : 0 < 4 * Real.pi * (beta / 64) := by positivity
    have hpi := Real.pi_gt_three
    have hT1 : (4 * Real.pi * (beta / 64))⁻¹ ≤ X ^ (2 ^ (μ + 1)) := by
      rw [show (4 * Real.pi * (beta / 64))⁻¹ = 16 / Real.pi * beta⁻¹ by field_simp; ring]
      have h16 : 16 / Real.pi ≤ X ^ (2 ^ μ) :=
        (div_le_self (by norm_num) (by linarith)).trans (hsmall 16 2 (by norm_num) hμ2)
      exact pw_mul hX (by positivity) (inv_pos.mpr b0).le h16 bi
    have hT11 : 1 ≤ X ^ (2 ^ (μ + 1)) := one_le_pw hX _
    have hscaled := section5LocalRefinementConstant_le_scaled 1 (4 * Real.pi * (beta / 64))
      (X ^ (2 ^ (μ + 1))) heta hT11 hT1
    have hK1 : polynomialPartitionConstant 1 = 16 := by
      norm_num [polynomialPartitionConstant, Nat.factorial]
    have hS1 : section5LocalRefinementConstant 1 1 ≤ X ^ (2 ^ μ) := by
      have h := s5_one_le (d := 1) le_rfl
      norm_num at h
      exact h.trans (pw_const hX (by
        have : (2 : Real) ^ (2 ^ 42) ≤ 2 ^ (2 ^ μ) :=
          pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_right (by norm_num) hμ)
        exact this) |>.trans le_rfl)
    unfold boundaryRefinementConstant
    refine hscaled.trans ?_
    rw [hK1]
    have hp16 := pw_pow hX (pow_nonneg hX0 _) (le_refl (X ^ (2 ^ (μ + 1)))) (show 16 ≤ 2 ^ 4 by norm_num)
    exact (pw_mul' hX (le_trans (by norm_num) (section5LocalRefinementConstant_ge_four _ _))
      (pow_nonneg (pow_nonneg hX0 _) _) hS1 hp16).trans (pw_mono hX le_rfl (by omega))
  have hcinv : (beta / (8 * boundaryRefinementConstant (beta / 64)))⁻¹ ≤ X ^ (2 ^ (μ + 8)) := by
    rw [inv_div, div_eq_mul_inv]
    have h8 := hsmall 8 2 (by norm_num) hμ2
    have h1 := pw_mul' hX (by norm_num) hCpos.le h8 hBRC
    exact (pw_mul' hX (by positivity) (inv_pos.mpr b0).le h1 bi).trans (pw_mono hX le_rfl (by omega))
  have hA : 1 + Real.log (max 1 (intervalDiscrepancyStepThreshold L delta beta T)) +
      |Real.log (beta / (8 * boundaryRefinementConstant (beta / 64)))| ≤
      Real.exp (X ^ (2 ^ (μ + 8) + 2)) := by
    have hlogT : Real.log (max 1 (intervalDiscrepancyStepThreshold L delta beta T)) ≤
        Real.exp (X ^ (2 ^ (μ + 8))) :=
      ((Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mpr hstep).trans
        (ex_mono hX le_rfl (by omega))
    have hlogc : |Real.log (beta / (8 * boundaryRefinementConstant (beta / 64)))| ≤
        Real.exp (X ^ (2 ^ (μ + 8))) := by
      rw [abs_of_nonpos (Real.log_nonpos hc0.le hc1), ← Real.log_inv]
      exact ((Real.log_le_sub_one_of_pos (inv_pos.mpr hc0)).trans (by linarith)).trans
        (ex_of_pw hcinv)
    have h1 : (1 : Real) ≤ Real.exp (X ^ (2 ^ (μ + 8))) := Real.one_le_exp (by positivity)
    exact exp_add_le hX (exp_add_le hX h1 hlogT) (hlogc.trans (exp_pow_mono hX (by omega)))
  unfold intervalDiscrepancyClosedThreshold
  have h := densityIterationClosedThreshold_le_double_exp_of_exp_budget _ _ _ _ _
    (2 ^ (μ + 2)) (2 ^ (μ + 2)) (2 ^ (μ + 8) + 2) (by positivity) hX hA hgain hbase (by
      have : 2 ^ (μ + 8) = 64 * 2 ^ (μ + 2) := by
        rw [show μ + 8 = (μ + 2) + 6 by ring, pow_add]; ring
      omega)
  refine h.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (pow_le_pow_right₀ hX1 ?_)))
  have : 2 ^ (μ + 9) = 2 * 2 ^ (μ + 8) := by rw [pow_succ]; ring
  have : 4 ≤ 2 ^ (μ + 8) := le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
  omega

/-! ### The comparison with the source -/

theorem double_exp_le_szemerediThreshold {L μ : Nat} (hL : 1 ≤ L) {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + 9)) :
    Real.exp (Real.exp ((2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)))) ≤
      szemerediThreshold delta L := by
  obtain ⟨ha0, -, -, hXu⟩ := intervalUniformityParameter_gen_bounds hL hδ hδhalf
  set u : Real := delta⁻¹ with hu'
  have hu : 2 ≤ u := by rw [hu', ← one_div, le_div_iff₀ hδ]; linarith
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu
  set q : Nat := 2 ^ (μ + 2 * L + 13) with hq
  set E : Nat := 2 ^ (2 ^ (L + 9)) with hE
  have hqE : q + 2 ≤ E := by
    have h2 : 2 ^ (μ + 2 * L + 14) = 2 * 2 ^ (μ + 2 * L + 13) := by
      rw [show μ + 2 * L + 14 = (μ + 2 * L + 13) + 1 by ring, pow_succ]; ring
    have h3 : 2 ≤ 2 ^ (μ + 2 * L + 13) :=
      le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h1 : q + 2 ≤ 2 ^ (μ + 2 * L + 14) := by rw [hq]; omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) hfit)
  have habsorb : (2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)) ≤ u ^ q := by
    have h := pow_le_pow_left₀ (by positivity) hXu (2 ^ (μ + 9))
    rw [← pow_mul, ← pow_add] at h
    rw [hq, show μ + 2 * L + 13 = 2 * L + 4 + (μ + 9) by ring]
    exact h
  have hx1 : 1 ≤ u ^ q := one_le_pow₀ hu1
  have hinner : 1 + 2 * u ^ q ≤ u ^ E := by
    calc
      _ ≤ u ^ q * 4 := by linarith only [hx1]
      _ ≤ u ^ q * u ^ 2 :=
          mul_le_mul_of_nonneg_left (by nlinarith only [hu] : (4 : Real) ≤ u ^ 2) (by positivity)
      _ = u ^ (q + 2) := (pow_add u q 2).symm
      _ ≤ _ := pow_le_pow_right₀ hu1 hqE
  have hexp : Real.exp (Real.exp (u ^ q)) ≤ (2 : Real) ^ ((2 : Real) ^ (u ^ E)) := by
    apply (section18_exp_le_two_rpow (Real.exp_pos _).le).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    calc
      2 * Real.exp (u ^ q) ≤ 2 * (2 : Real) ^ (2 * u ^ q) :=
        mul_le_mul_of_nonneg_left (section18_exp_le_two_rpow (by positivity)) (by norm_num)
      _ = (2 : Real) ^ (1 + 2 * u ^ q) := by
        rw [Real.rpow_add (by norm_num : (0 : Real) < 2), Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hinner
  refine (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr habsorb)).trans (hexp.trans (le_of_eq ?_))
  unfold szemerediThreshold
  rw [hE, ← hu']
  simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]

/-! ### Theorem 18.2 -/

/-- **Theorem 18.2 at length `L` from a degree-`(L−2)` envelope.** -/
theorem theorem182At_of_envBound {L μ : Nat} (hL : 3 ≤ L) (henv : EnvBound (L - 2) μ)
    (hμ : 42 ≤ μ) (hLμ : 4 * L + 20 ≤ 2 ^ μ) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + 9)) :
    Theorem182At L := by
  intro delta N hδ hδhalf hN A hA hcard
  obtain ⟨ha0, haδ, -, -⟩ := intervalUniformityParameter_gen_bounds (by omega : 1 ≤ L) hδ hδhalf
  have ha2 : intervalUniformityParameter delta L ≤ 1 / 2 := haδ.trans hδhalf
  obtain ⟨beta, sigma, T, hB, b0, b1, s0, -, bi, si, Ti⟩ := henv _ ha0 ha2
  have hclosed := closedThreshold_le_of_env (by omega : 1 ≤ L) hδ hδhalf hμ hLμ b0 b1 s0 bi si Ti
  have hsrc := double_exp_le_szemerediThreshold (by omega : 1 ≤ L) hδ hδhalf hfit
  exact FunctionDiscrepancyBound.natural_szemeredi_closed (k := L) (by omega) hδ b0 s0 hB N
    ((hclosed.trans hsrc).trans hN) A hA hcard

end LeanProofs.GowersSzemeredi
