import GowersSzemeredi.Proofs18EnvelopeBounds
import GowersSzemeredi.Proofs18ExponentialCalculus
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

/-! ### Parameterized thresholds -/

/-- The Theorem 18.2 threshold with `k + c` in place of the printed `k + 9`. -/
def szemerediThresholdAt (c : Nat) (delta : Real) (k : Nat) : Real :=
  (2 : Real) ^
    ((2 : Real) ^
      (delta⁻¹ ^ ((2 : Real) ^ ((2 : Real) ^ (k + c : Nat)))))

/-- Theorem 18.2 at length `k` with the threshold `szemerediThresholdAt c`. -/
def Theorem182AtSharp (c k : Nat) : Prop :=
  ∀ (delta : Real) (N : Nat), 0 < delta → delta ≤ 1 / 2 →
    szemerediThresholdAt c delta k ≤ N →
    ∀ A : Finset Nat, A ⊆ Finset.Icc 1 N → delta * N ≤ A.card → HasNatAP A k

/-- At `c = 9` it is the catalogue's Theorem 18.2 at length `k`. -/
theorem theorem182AtSharp_nine_iff (k : Nat) : Theorem182AtSharp 9 k ↔ Theorem182At k :=
  Iff.rfl

/-! ### The uniformity parameter -/

theorem interval_exponent_le (L : Nat) : 1 + (4 * L + 9) * 2 ^ (L - 1) ≤ 2 ^ (2 * L + 4) := by
  have hL : L < 2 ^ L := Nat.lt_two_pow_self
  have hpow : 1 ≤ 2 ^ (L - 1) := Nat.one_le_two_pow
  have hcoef : 4 * L + 10 ≤ 2 ^ (L + 4) := by
    rw [pow_add]
    norm_num only [Nat.reducePow]
    omega
  calc
    _ ≤ (4 * L + 10) * 2 ^ (L - 1) := by nlinarith only [hpow]
    _ ≤ 2 ^ (L + 4) * 2 ^ L :=
      Nat.mul_le_mul hcoef (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le L 1))
    _ = _ := by rw [← pow_add]; congr 1; omega

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
    exact (pw_mul hX (inv_pos.mpr b0).le h8 bi).trans (pw_mono hX le_rfl (by omega))
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
      exact (pw_mul hX (inv_pos.mpr b0).le (hsmall 32 3 (by norm_num) (by omega)) bi).trans
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
      exact (pw_mul hX (by positivity) hc hu).trans (pw_mono hX le_rfl (by omega))
    unfold intervalDiscrepancyStepThreshold
    apply max_le (Real.one_le_exp (by positivity))
    apply max_le (hdex _ (hLX.trans (pw_X hX _)))
    refine max_le (dex_mono hX Ti (by omega)) (max_le (hdex _ h32) (hdex _ hden))
  -- the length factor `c`
  have hS1 : section5LocalRefinementConstant 1 1 ≤ X ^ (2 ^ μ) :=
    hsmall _ 42 (by simpa using (s5_one_le (d := 1) le_rfl)) hμ
  obtain ⟨hc0, hc1, hci⟩ := interval_length_factor_bounds_of_powers hX b0 b1 bi hS1
  have hcinv : (beta / (8 * boundaryRefinementConstant (beta / 64)))⁻¹ ≤ X ^ (2 ^ (μ + 8)) := by
    refine hci.trans (pow_le_pow_right₀ hX1 ?_)
    have hpow : 1 ≤ 2 ^ μ := Nat.one_le_two_pow
    rw [pow_add]
    norm_num only [Nat.reducePow]
    omega
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

theorem double_exp_le_szemerediThresholdAt {L μ c : Nat} (hL : 1 ≤ L) {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + c)) :
    Real.exp (Real.exp ((2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)))) ≤
      szemerediThresholdAt c delta L := by
  obtain ⟨ha0, -, -, hXu⟩ := intervalUniformityParameter_gen_bounds hL hδ hδhalf
  set u : Real := delta⁻¹ with hu'
  have hu : 2 ≤ u := by rw [hu', ← one_div, le_div_iff₀ hδ]; linarith
  set q : Nat := 2 ^ (μ + 2 * L + 13) with hq
  set E : Nat := 2 ^ (2 ^ (L + c)) with hE
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
  have hexp := exp_exp_pow_le_two_rpow_two_rpow hu hqE
  refine (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr habsorb)).trans (hexp.trans (le_of_eq ?_))
  unfold szemerediThresholdAt
  rw [hE, ← hu']
  simp only [← Real.rpow_natCast, Nat.cast_pow, Nat.cast_ofNat]

theorem theorem182AtSharp_of_envBound {L μ c : Nat} (hL : 3 ≤ L) (henv : EnvBound (L - 2) μ)
    (hμ : 42 ≤ μ) (hLμ : 4 * L + 20 ≤ 2 ^ μ) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + c)) :
    Theorem182AtSharp c L := by
  intro delta N hδ hδhalf hN A hA hcard
  obtain ⟨ha0, haδ, -, -⟩ := intervalUniformityParameter_gen_bounds (by omega : 1 ≤ L) hδ hδhalf
  have ha2 : intervalUniformityParameter delta L ≤ 1 / 2 := haδ.trans hδhalf
  obtain ⟨beta, sigma, T, hB, b0, b1, s0, -, bi, si, Ti⟩ := henv _ ha0 ha2
  have hclosed := closedThreshold_le_of_env (by omega : 1 ≤ L) hδ hδhalf hμ hLμ b0 b1 s0 bi si Ti
  have hsrc := double_exp_le_szemerediThresholdAt (by omega : 1 ≤ L) hδ hδhalf hfit
  exact FunctionDiscrepancyBound.natural_szemeredi_closed (k := L) (by omega) hδ b0 s0 hB N
    ((hclosed.trans hsrc).trans hN) A hA hcard

/-! ### The printed threshold as the offset-nine specialization -/

theorem double_exp_le_szemerediThreshold {L μ : Nat} (hL : 1 ≤ L) {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + 9)) :
    Real.exp (Real.exp ((2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)))) ≤
      szemerediThreshold delta L :=
  double_exp_le_szemerediThresholdAt (c := 9) hL hδ hδhalf hfit

/-- **Theorem 18.2 at length `L` from a degree-`(L−2)` envelope.** -/
theorem theorem182At_of_envBound {L μ : Nat} (hL : 3 ≤ L) (henv : EnvBound (L - 2) μ)
    (hμ : 42 ≤ μ) (hLμ : 4 * L + 20 ≤ 2 ^ μ) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + 9)) :
    Theorem182At L :=
  theorem182AtSharp_of_envBound (c := 9) hL henv hμ hLμ hfit

end LeanProofs.GowersSzemeredi
