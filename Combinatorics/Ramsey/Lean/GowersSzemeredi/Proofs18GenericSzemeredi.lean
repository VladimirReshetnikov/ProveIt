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
  once `μ + 2L + 14 ≤ 2^(L+9)`.

`double_exp_le_szemerediThreshold` and `theorem182At_of_envBound` are in
`Proofs18GenericSzemerediSide`, outside the final route. -/
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
  have hu : 2 ≤ delta⁻¹ := by rw [← one_div, le_div_iff₀ hδ]; linarith
  have hL1 : (1 : Real) ≤ L := by exact_mod_cast hL
  unfold intervalUniformityParameter
  set b := delta ^ L / (512 * (L : Real) ^ 3) with hb
  have hb0 : 0 < b := by positivity
  have hbL : b ≤ delta ^ L :=
    div_le_self (by positivity) (by linarith [one_le_pow₀ hL1 (n := 3)])
  have hb2 : b ≤ ((2 : Real) ^ L)⁻¹ :=
    hbL.trans ((pow_le_pow_left₀ hδ.le hδhalf L).trans_eq (by rw [one_div, inv_pow]))
  have hα : b ^ (2 ^ (L - 1)) ≤ b := pow_le_of_le_one hb0.le
    (hb2.trans (inv_le_one_of_one_le₀ (one_le_pow₀ one_le_two))) (by positivity)
  refine ⟨pow_pos hb0 _, hα.trans (hbL.trans (pow_le_of_le_one hδ.le (by linarith) (by omega))),
    ?_, ?_⟩
  · -- `2/α ≥ 2/b ≥ 2^L`
    rw [le_div_iff₀ (pow_pos hb0 _)]
    calc (2 : Real) ^ L * b ^ (2 ^ (L - 1)) ≤ 2 ^ L * ((2 : Real) ^ L)⁻¹ := by
          gcongr; exact hα.trans hb2
      _ ≤ 2 := (mul_inv_cancel₀ (by positivity)).le.trans one_le_two
  · -- `b⁻¹ = 512 L³ u^L ≤ u^(4L+9)`
    have hbi : b⁻¹ ≤ delta⁻¹ ^ (4 * L + 9) := by
      have hL2 : (L : Real) ≤ delta⁻¹ ^ L :=
        (by exact_mod_cast Nat.lt_two_pow_self.le : (L : Real) ≤ 2 ^ L).trans
          (pow_le_pow_left₀ (by norm_num) hu L)
      rw [hb, inv_div, div_eq_mul_inv, ← inv_pow]
      calc 512 * (L : Real) ^ 3 * delta⁻¹ ^ L ≤
            delta⁻¹ ^ 9 * (delta⁻¹ ^ L) ^ 3 * delta⁻¹ ^ L := by
            gcongr; linarith [pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2) hu 9]
        _ = delta⁻¹ ^ (4 * L + 9) := by ring
    rw [div_eq_mul_inv, ← inv_pow]
    calc 2 * b⁻¹ ^ (2 ^ (L - 1)) ≤ delta⁻¹ * (delta⁻¹ ^ (4 * L + 9)) ^ (2 ^ (L - 1)) := by
          gcongr
      _ = delta⁻¹ ^ (1 + (4 * L + 9) * 2 ^ (L - 1)) := by ring
      _ ≤ delta⁻¹ ^ (2 ^ (2 * L + 4)) :=
        pow_le_pow_right₀ (le_trans (by norm_num) hu) (interval_exponent_le L)

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
  set alpha := intervalUniformityParameter delta L
  set X := 2 / alpha with hXdef
  have hX : 2 ≤ X := (le_self_pow₀ one_le_two (by omega)).trans h2L
  have hX1 : (1 : Real) ≤ X := by linarith
  have hδi : delta⁻¹ ≤ X := (inv_anti₀ ha0 haδ).trans (by
    rw [hXdef, div_eq_mul_inv]; exact le_mul_of_one_le_left (inv_pos.mpr ha0).le one_le_two)
  have hLX : (L : Real) ≤ X :=
    (by exact_mod_cast Nat.lt_two_pow_self.le : (L : Real) ≤ 2 ^ L).trans h2L
  have hsmall : ∀ c : Real, ∀ j : Nat, c ≤ 2 ^ (2 ^ j) → j ≤ μ → c ≤ X ^ (2 ^ μ) :=
    fun c j hc hj => pw_mono hX (pw_const hX hc) hj
  -- the gain `β/8` and the base `2 max 1 (σ/16)⁻¹`
  have hgain : (beta / 8)⁻¹ ≤ X ^ (2 ^ (μ + 2)) := by
    rw [show (beta / 8)⁻¹ = 8 * beta⁻¹ by field_simp]
    exact (pw_mul hX (inv_pos.mpr b0).le (hsmall 8 2 (by norm_num) (by omega)) bi).trans
      (pw_mono hX le_rfl (by omega))
  have hbase : 2 * max 1 (sigma / 16)⁻¹ ≤ Real.exp (X ^ (2 ^ (μ + 2))) := by
    rw [show (sigma / 16)⁻¹ = 16 * sigma⁻¹ by field_simp]
    exact ex_mul hX (by positivity) (ex_of_pw (hX.trans (pw_X hX _)))
      (max_le (Real.one_le_exp (by positivity)) (ex_mul hX (inv_pos.mpr s0).le
        (ex_of_pw (hsmall 16 2 (by norm_num) (by omega))) si))
  -- the step threshold
  have hdex (x : Real) (hx : x ≤ X ^ (2 ^ (μ + 2))) :
      x ≤ Real.exp (Real.exp (X ^ (2 ^ (μ + 2)))) := le_exp_exp_of_le_exp (ex_of_pw hx)
  have h32 : 32 / beta ≤ X ^ (2 ^ (μ + 2)) := by
    rw [div_eq_mul_inv]
    exact (pw_mul hX (inv_pos.mpr b0).le (hsmall 32 3 (by norm_num) (by omega)) bi).trans
      (pw_mono hX le_rfl (by omega))
  have hden : (512 * (L : Real) ^ 2 + 1) / delta ^ L ≤ X ^ (2 ^ (μ + 2)) := by
    have hc : 512 * (L : Real) ^ 2 + 1 ≤ X ^ (2 ^ μ) := by
      refine le_trans ?_ (pw_natpow hX (n := 12) (by omega))
      linarith [pow_le_pow_left₀ (Nat.cast_nonneg L) hLX 2, one_le_pow₀ hX1 (n := 2),
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hX 10) (sq_nonneg X)]
    rw [div_eq_mul_inv, ← inv_pow]
    exact (pw_mul hX (by positivity) hc ((pow_le_pow_left₀ (inv_pos.mpr hδ).le hδi L).trans
      (pw_natpow hX (by omega)))).trans (pw_mono hX le_rfl (by omega))
  have hstep : max 1 (intervalDiscrepancyStepThreshold L delta beta T) ≤
      Real.exp (Real.exp (X ^ (2 ^ (μ + 2)))) :=
    max_le (Real.one_le_exp (by positivity)) (max_le (hdex _ (hLX.trans (pw_X hX _)))
      (max_le (dex_mono hX Ti (by omega)) (max_le (hdex _ h32) (hdex _ hden))))
  -- the length factor `c`
  obtain ⟨hc0, hc1, hci⟩ := interval_length_factor_bounds_of_powers hX b0 b1 bi
    (hsmall _ 42 (by simpa using (s5_one_le (d := 1) le_rfl)) hμ)
  have hcinv : (beta / (8 * boundaryRefinementConstant (beta / 64)))⁻¹ ≤ X ^ (2 ^ (μ + 8)) := by
    refine hci.trans (pow_le_pow_right₀ hX1 ?_)
    have := Nat.one_le_two_pow (n := μ)
    rw [pow_add 2 μ 8]
    omega
  have hA : 1 + Real.log (max 1 (intervalDiscrepancyStepThreshold L delta beta T)) +
      |Real.log (beta / (8 * boundaryRefinementConstant (beta / 64)))| ≤
      Real.exp (X ^ (2 ^ (μ + 8) + 2)) := by
    have hlogT := ((Real.log_le_iff_le_exp (by positivity)).mpr hstep).trans
      (ex_mono hX le_rfl (show μ + 2 ≤ μ + 8 by omega))
    have hlogc : |Real.log (beta / (8 * boundaryRefinementConstant (beta / 64)))| ≤
        Real.exp (X ^ (2 ^ (μ + 8))) := by
      rw [abs_of_nonpos (Real.log_nonpos hc0.le hc1), ← Real.log_inv]
      exact (Real.log_le_self (inv_nonneg.mpr hc0.le)).trans (ex_of_pw hcinv)
    exact exp_add_le hX (exp_add_le hX (Real.one_le_exp (by positivity)) hlogT)
      (hlogc.trans (exp_pow_mono hX (by omega)))
  refine (densityIterationClosedThreshold_le_double_exp_of_exp_budget _ _ _ _ _
    (2 ^ (μ + 2)) (2 ^ (μ + 2)) (2 ^ (μ + 8) + 2) (by positivity) hX hA hgain hbase
    (by rw [pow_add 2 μ 2, pow_add 2 μ 8]; omega)).trans
    (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (pow_le_pow_right₀ hX1 ?_)))
  have := Nat.one_le_two_pow (n := μ)
  rw [pow_add 2 μ 8, pow_add 2 μ 9]
  omega

/-! ### The comparison with the source -/

theorem double_exp_le_szemerediThresholdAt {L μ c : Nat} (hL : 1 ≤ L) {delta : Real}
    (hδ : 0 < delta) (hδhalf : delta ≤ 1 / 2) (hfit : μ + 2 * L + 14 ≤ 2 ^ (L + c)) :
    Real.exp (Real.exp ((2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)))) ≤
      szemerediThresholdAt c delta L := by
  obtain ⟨ha0, -, -, hXu⟩ := intervalUniformityParameter_gen_bounds hL hδ hδhalf
  have hu : 2 ≤ delta⁻¹ := by rw [← one_div, le_div_iff₀ hδ]; linarith
  have hqE : 2 ^ (μ + 2 * L + 13) + 2 ≤ 2 ^ (2 ^ (L + c)) := by
    refine le_trans ?_ (Nat.pow_le_pow_right two_pos hfit)
    have := Nat.lt_two_pow_self (n := μ + 2 * L + 13)
    rw [show μ + 2 * L + 14 = μ + 2 * L + 13 + 1 by omega, pow_succ 2 (μ + 2 * L + 13)]
    omega
  have habsorb : (2 / intervalUniformityParameter delta L) ^ (2 ^ (μ + 9)) ≤
      delta⁻¹ ^ 2 ^ (μ + 2 * L + 13) := by
    rw [show μ + 2 * L + 13 = 2 * L + 4 + (μ + 9) by omega, pow_add 2 (2 * L + 4), pow_mul]
    gcongr
  refine (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr habsorb)).trans
    ((exp_exp_pow_le_two_rpow_two_rpow hu hqE).trans_eq ?_)
  unfold szemerediThresholdAt
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

end LeanProofs.GowersSzemeredi
