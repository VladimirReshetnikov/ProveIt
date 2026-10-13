import GowersSzemeredi.Proofs18FejerEnvelopeBase
import GowersSzemeredi.Proofs18TightClassesFejer
import GowersSzemeredi.Proofs16UniformCoverTwoSplit
import GowersSzemeredi.Proofs16WeylBudgetGrowth
import GowersSzemeredi.Proofs18CoverSharperLowDegrees
import GowersSzemeredi.Proofs18CoverSharperShortLengths
import GowersSzemeredi.Proofs18EtaStepSmall
import GowersSzemeredi.Proofs18JointSliceInverseFejer

/-! **The final route, part 1: the class table** (Notes L.16-final).

The classes `tDegT3` of the two-track split (Notes L.16x/y) and their
polynomial covers (`polyCoverAt_classT3`), with the base envelope bounds of
the Fejér route (`Proofs18FejerEnvelopeBase`, Notes L.16): the declarations of
the class modules that the final route uses, in their original order
(extracted by `assemble_final.py`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section Fixed

variable {alpha : Real}

/-- `θ₁′⁻¹ ≤ X^(2^(5k+16))`. -/
theorem thetaOne_fejer_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < fejerThetaOne alpha (alpha / 2) k ∧ fejerThetaOne alpha (alpha / 2) k ≤ 1 ∧
      (fejerThetaOne alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (5 * k + 16)) := by
  obtain ⟨h0, h1⟩ := fejer_alpha_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  have hq0 : 0 < alpha * (alpha / 2) / 4 := by positivity
  refine ⟨by linarith, by linarith, ?_⟩
  unfold fejerThetaOne
  rw [← inv_pow]
  have hq := quarter_base_inv_le ha ha2
  have hF := fejerProductExponent_le k
  calc (alpha * (alpha / 2) / 4)⁻¹ ^ fejerProductExponent k
      ≤ ((2 / alpha) ^ 3) ^ fejerProductExponent k := pow_le_pow_left₀ (inv_pos.mpr hq0).le hq _
    _ = (2 / alpha) ^ (3 * fejerProductExponent k) := by rw [← pow_mul]
    _ ≤ (2 / alpha) ^ (2 ^ (5 * k + 16)) := by
        apply pow_le_pow_right₀ (le_trans (by norm_num) hX)
        have h : 2 ^ (5 * k + 16) = 4 * 2 ^ (5 * k + 14) := by
          rw [show 5 * k + 16 = (5 * k + 14) + 2 by ring, pow_add]; ring
        omega

theorem thetaTwo_fejer_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16ThetaTwo (fejerThetaOne alpha (alpha / 2) k) ∧
      section16ThetaTwo (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16ThetaTwo (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤
        (2 / alpha) ^ (2 ^ ((5 * k + 14) + 6)) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le_with (fejer_alpha_bounds k ha ha2).1 (fejer_alpha_bounds k ha ha2).2
  obtain ⟨t0, -, ti⟩ := thetaOne_fejer_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  have hX0 : (0 : Real) ≤ 2 / alpha := by linarith
  refine ⟨h0, h1, ?_⟩
  unfold section16ThetaTwo
  have h32 : ((2 : Real) ^ (-(32 : Real)))⁻¹ ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2)) := by
    rw [Real.rpow_neg (by norm_num), inv_inv,
      show (32 : Real) = ((32 : Nat) : Real) by norm_num, Real.rpow_natCast]
    refine (pow_le_pow_left₀ (by norm_num) hX 32).trans (pw_natpow hX ?_)
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ ((5 * k + 14) + 2) := Nat.pow_le_pow_right (by norm_num) (by
          omega)
  have h8 : ((fejerThetaOne alpha (alpha / 2) k) ^ 8)⁻¹ ≤
      (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2 + 3)) := by
    rw [← inv_pow]
    exact pw_pow hX (inv_pos.mpr t0).le ti (by norm_num)
  rw [mul_inv]
  have := pw_mul hX (by positivity) (by positivity) (pw_mono hX h32 (by omega)) h8
  exact pw_mono hX this (by omega)

theorem budget_fejer_bounds5 (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ∧ globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ≤ 1 ∧
      (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (5 * k + 21)) := by
  obtain ⟨h0, h1, hi⟩ := thetaTwo_fejer_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  have hden : (1 : Real) ≤ 2 * (2 ^ k + 1) := by
    have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    linarith
  unfold globalBudgetW
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · rw [inv_div, div_eq_mul_inv]
    have hc : 2 * ((2 : Real) ^ k + 1) ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 6)) := by
      have h1 : 2 * ((2 : Real) ^ k + 1) ≤ 2 ^ (k + 2) := by
        have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        rw [pow_add]; norm_num; linarith
      refine h1.trans ((pow_le_pow_left₀ (by norm_num) hX _).trans (pw_natpow hX ?_))
      calc k + 2 ≤ 2 ^ (k + 2) := Nat.lt_two_pow_self.le
        _ ≤ 2 ^ ((5 * k + 14) + 6) := Nat.pow_le_pow_right (by norm_num) (by
            have : k + 2 ≤ (5 * k + 14) := by
              have := Nat.lt_two_pow_self (n := k + 5); omega
            omega)
    have := pw_mul hX (by positivity) (inv_pos.mpr h0).le hc hi
    exact this

theorem T2_fejer_bounds5 (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ∧ globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (globalTheta2W (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ (5 * k + 21)) := by
  obtain ⟨h0, h1, hi⟩ := thetaTwo_fejer_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  unfold globalTheta2W
  refine ⟨by positivity, by linarith, ?_⟩
  rw [inv_div, div_eq_mul_inv]
  have h2 : (2 : Real) ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 6)) :=
    hX.trans (pw_X hX _)
  have := pw_mul hX (by norm_num) (inv_pos.mpr h0).le h2 hi
  exact pw_mono hX this (by omega)

theorem delta_fejer_bounds5 (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Delta (fejerThetaOne alpha (alpha / 2) k) ∧
      section16Delta (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16Delta (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ (5 * k + 21)) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨-, -, d0, d1⟩ := section16_theta_delta_bounds_with (fejer_alpha_bounds k ha ha2).1 (fejer_alpha_bounds k ha ha2).2
  obtain ⟨t0, t1, ti⟩ := thetaOne_fejer_bounds k ha ha2
  have hX := two_div_ge_two ha ha2
  refine ⟨d0, d1, ?_⟩
  set t := fejerThetaOne alpha (alpha / 2) k with htdef
  have hq0 : 0 < t / 4 := by positivity
  have hq1 : t / 4 ≤ 1 := by linarith
  -- `(t/4)^(11/2) ≥ (t/4)^6`
  have h6 : (t / 4) ^ (6 : Nat) ≤ (t / 4) ^ ((11 : Real) / 2) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hq0 hq1 (by norm_num)
  unfold section16Delta
  have h37 : ((2 : Real) ^ (-(37 : Real)))⁻¹ = 2 ^ (37 : Nat) := by
    rw [Real.rpow_neg (by norm_num), inv_inv,
      show (37 : Real) = ((37 : Nat) : Real) by norm_num, Real.rpow_natCast]
  rw [mul_inv, h37]
  have hinv6 : ((t / 4) ^ ((11 : Real) / 2))⁻¹ ≤ ((t / 4) ^ (6 : Nat))⁻¹ :=
    inv_anti₀ (pow_pos hq0 _) h6
  have hq : ((t / 4) ^ (6 : Nat))⁻¹ ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2 + 1 + 3)) := by
    rw [← inv_pow, inv_div]
    have h4t : 4 / t ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2 + 1)) := by
      rw [div_eq_mul_inv]
      have h4 : (4 : Real) ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2)) :=
        (show (4 : Real) ≤ 2 ^ 2 by norm_num).trans
          ((pow_le_pow_left₀ (by norm_num) hX 2).trans (pw_natpow hX (by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ ((5 * k + 14) + 2) := Nat.pow_le_pow_right (by norm_num) (by
                  have := Nat.one_le_two_pow (n := k + 5); omega))))
      exact pw_mul hX (by norm_num) (inv_pos.mpr t0).le h4 ti
    exact pw_pow hX (by positivity) h4t (by norm_num)
  have h2 : (2 : Real) ^ (37 : Nat) ≤ (2 / alpha) ^ (2 ^ ((5 * k + 14) + 2 + 1 + 3)) :=
    (pow_le_pow_left₀ (by norm_num) hX 37).trans (pw_natpow hX (by
      calc 37 ≤ 2 ^ 6 := by norm_num
        _ ≤ 2 ^ ((5 * k + 14) + 2 + 1 + 3) := Nat.pow_le_pow_right (by norm_num) (by
            have := Nat.one_le_two_pow (n := k + 5); omega)))
  have := pw_mul hX (by positivity) (by positivity) h2 (hinv6.trans hq)
  exact pw_mono hX this (by omega)

end Fixed

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The family exponent of the small dimension-two seed. -/
def splitSeedSmallA : Nat := 32

/-- The parameter degree of the small dimension-two seed. -/
def splitSeedSmallD : Nat := 2 ^ 48

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The polynomial base-budget degree of the Fejér fixed parameters. -/
def pDeg (k : Nat) : Nat := 5 * k + 21

theorem seven_le_pDeg (k : Nat) : 7 ≤ pDeg k := by unfold pDeg; omega

theorem five_k_le_pDeg (k : Nat) : 5 * k + 21 ≤ pDeg k := le_rfl

theorem k_succ_le_two_pow_pDeg (k : Nat) : k + 1 ≤ 2 ^ pDeg k := by
  have h : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
  exact h.le.trans (Nat.pow_le_pow_right (by norm_num) (by unfold pDeg; omega))

/-- `uCount_scale_le` at any budget degree `b ≥ 7`. -/
theorem uCount_scale_le_deg {X V γ θ s : Real} {D μV μD μ0 c : Nat} (hX : 2 ≤ X) (hV : 1 ≤ V)
    (hVμ : V ≤ 2 ^ (2 ^ μV)) {b : Nat} (h7 : 7 ≤ b) (hμ0 : max μV b + 2 ≤ μ0)
    (hg : 0 < γ) (hg1 : γ ≤ 1) (hgi : γ⁻¹ ≤ X ^ (2 ^ b))
    (ht : 0 < θ) (ht1 : θ ≤ 1) (hti : θ⁻¹ ≤ X ^ (2 ^ b))
    (hs : 0 < s) (hs1 : s ≤ 1) (hsi : s⁻¹ ≤ X ^ (2 ^ c)) (hD : D ≤ 2 ^ μD) :
    uCount V D γ θ s ≤ X ^ (2 ^ (max μ0 c + 1 + μD)) := by
  rw [uCount_eq hV D hg hg1 ht ht1 hs hs1]
  have hval : uniformBase V 1 θ γ s = 4 * V * γ⁻¹ * θ⁻¹ * s⁻¹ := by
    unfold uniformBase; field_simp; ring
  rw [hval]
  set m := max μV b
  have h7m : 7 ≤ m := le_trans h7 (le_max_right μV b)
  have h4 : (4 : Real) ≤ X ^ (2 ^ m) := pw_const hX (by
    have : 2 ≤ 2 ^ m := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc (4 : Real) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 ^ m) := pow_le_pow_right₀ (by norm_num) this)
  have hV' : V ≤ X ^ (2 ^ m) := pw_mono hX (pw_const hX hVμ) (le_max_left _ _)
  have hg' : γ⁻¹ ≤ X ^ (2 ^ m) := pw_mono hX hgi (le_max_right _ _)
  have ht' : θ⁻¹ ≤ X ^ (2 ^ m) := pw_mono hX hti (le_max_right _ _)
  have h1 := pw_mul hX (by norm_num) (by linarith) h4 hV'
  have h2 := pw_mul hX (inv_pos.mpr hg).le (inv_pos.mpr ht).le hg' ht'
  have h3 := pw_mul hX (by positivity) (by positivity) h1 h2
  have hc0 : 4 * V * γ⁻¹ * θ⁻¹ ≤ X ^ (2 ^ μ0) := by
    rw [show 4 * V * γ⁻¹ * θ⁻¹ = 4 * V * (γ⁻¹ * θ⁻¹) by ring]
    exact pw_mono hX h3 (by omega)
  have h5 := pw_mul' hX (by positivity) (inv_pos.mpr hs).le hc0 hsi
  exact pw_pow hX (by positivity) h5 hD

namespace GenParams

variable {alpha : Real}

/-- `(α/2)⁻¹ ≤ X^(2^b)` at any degree. -/
theorem half_inv_le_deg (b : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    (alpha / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ b) := by
  rw [inv_div]; exact pw_X (two_div_ge_two ha ha2) _

end GenParams

section Fixed

variable {alpha : Real}

theorem budget_gen_bounds_fejerW (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ∧
      globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k ≤ 1 ∧
      (globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ pDeg k) :=
  budget_fejer_bounds5 k ha ha2

theorem T2_gen_bounds_fejerW (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ∧
      globalTheta2W (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (globalTheta2W (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ pDeg k) :=
  T2_fejer_bounds5 k ha ha2

theorem delta_gen_bounds_fejerW (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Delta (fejerThetaOne alpha (alpha / 2) k) ∧
      section16Delta (fejerThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16Delta (fejerThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ pDeg k) :=
  delta_fejer_bounds5 k ha ha2

/-- **The Fejér base density is a reciprocal power, at the polynomial budget `pDeg`.** -/
theorem baseCFW_recipPowerLB {V : Real} {D k μV μ0 : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (pDeg k) + 2 ≤ μ0) :
    RecipPowerLB (2 / alpha) (baseCF V D k alpha) (D * 2 ^ μ0 + 1) (D + 1) := by
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejerW k ha ha2
  exact uniform_baseC_recipPowerLB_of_budget ha ha2 hV hVμ hB0 hB1 (seven_le_pDeg k) hBi hμ0

end Fixed

/-- The polynomial bound on the class base. -/
def tightMuW (k : Nat) : Nat := 4 * k + 13

/-- **The class base from polynomial family constants**: `V ≤ 2^(2^(4k+13))`. -/
theorem classV_le_poly (Kc pc : Nat → Nat)
    (hconst : ∀ k, (Kc k : Real) + pc k ≤ 2 ^ ((2 : Nat) ^ (4 * k + 16))) (k : Nat) :
    classV Kc pc k ≤ 2 ^ (2 ^ tightMuW k) := by
  set E := (2 : Nat) ^ (4 * k + 12) with hE
  have hterm : ∀ j ∈ Finset.range k, (Kc j : Real) + pc j ≤ 2 ^ E := by
    intro j hj
    have hjk : 4 * j + 16 ≤ 4 * k + 12 := by have := Finset.mem_range.mp hj; omega
    refine (hconst j).trans (pow_le_pow_right₀ (by norm_num) ?_)
    exact Nat.pow_le_pow_right (by norm_num) hjk
  have hsum : ∑ j ∈ Finset.range k, ((Kc j : Real) + pc j) ≤ k * 2 ^ E := by
    have := Finset.sum_le_sum hterm
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hE1 : (1 : Real) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hk1 : ((k : Real) + 1) ≤ 2 ^ (k + 1) := by
    have h : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    exact_mod_cast h.le
  have hkE : k + 1 + E ≤ 2 ^ tightMuW k := by
    have h1 : k + 1 < 2 ^ (k + 1) := Nat.lt_two_pow_self
    have h2 : 2 ^ (k + 1) ≤ E := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ tightMuW k = 2 * E := by
      unfold tightMuW; rw [hE, show 4 * k + 13 = (4 * k + 12) + 1 by ring, pow_succ]; ring
    omega
  calc classV Kc pc k ≤ ((k : Real) + 1) * 2 ^ E := by
        unfold classV
        nlinarith
    _ ≤ 2 ^ (k + 1) * 2 ^ E := mul_le_mul_of_nonneg_right hk1 (by positivity)
    _ = 2 ^ (k + 1 + E) := by rw [pow_add (2 : Real) (k + 1) E]
    _ ≤ 2 ^ (2 ^ tightMuW k) := pow_le_pow_right₀ (by norm_num) hkE

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- **The split step at any exponent and slack.** -/
theorem split_step_gen {k a D a' D' P T e s : Nat} (ha : 1 ≤ a)
    (hA : 2 ^ (k + 6) * a ≤ 2 ^ e) (hDb : D ≤ 2 ^ (e + s))
    (ha' : a' ≤ 2 ^ (k + 5) * (a * a)) (hD' : D' ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T)
    (hP : P ≤ 2 ^ (5 * k + 20)) (hT : T ≤ 2 ^ (5 * k + 19)) :
    2 ^ (k + 1 + 6) * a' ≤ 2 ^ (2 * e) ∧ D' ≤ 2 ^ (2 * e + s + (5 * k + 22)) := by
  constructor
  · calc 2 ^ (k + 1 + 6) * a' ≤ 2 ^ (k + 1 + 6) * (2 ^ (k + 5) * (a * a)) :=
          Nat.mul_le_mul_left _ ha'
      _ = (2 ^ (k + 6) * a) * (2 ^ (k + 6) * a) := by ring
      _ ≤ 2 ^ e * 2 ^ e := Nat.mul_le_mul hA hA
      _ = 2 ^ (2 * e) := by rw [← pow_add, two_mul]
  · set X := 2 ^ e with hXdef
    set Y := 2 ^ (e + s) with hYdef
    set Z := 2 ^ (5 * k + 19) with hZdef
    have haX : a ≤ X := le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
    have hXY : X ≤ Y := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hsum : a + D ≤ 2 * Y := by omega
    have e20 : 2 ^ (5 * k + 20) = 2 * Z := by
      rw [hZdef, show 5 * k + 20 = (5 * k + 19) + 1 by ring, pow_succ]; ring
    have hX1 : 1 ≤ X := Nat.one_le_two_pow
    have hY1 : 1 ≤ Y := Nat.one_le_two_pow
    have hprod : 8 * Z * X * Y = 2 ^ (2 * e + s + (5 * k + 22)) := by
      rw [hXdef, hYdef, hZdef, show 2 * e + s + (5 * k + 22) = e + (e + s) + ((5 * k + 19) + 3) by ring,
        pow_add, pow_add, pow_add]
      ring
    calc D' ≤ 2 ^ (k + 6) * (a * (a + D)) * P + T := hD'
      _ = (2 ^ (k + 6) * a) * (a + D) * P + T := by ring
      _ ≤ X * (2 * Y) * (2 * Z) + Z :=
          Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul hA hsum) (e20 ▸ hP)) hT
      _ ≤ 8 * Z * X * Y := split_step_arith _ _ _ hX1 hY1
      _ = _ := hprod

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The family exponent of the next split class, combined by `max`. -/
def splitStepAMax (k a : Nat) : Nat := max (sCountN k a) (sExpN k a)

/-- The parameter degree with general step inputs, combined by `max`. -/
def splitStepDMaxWith (P T k a D : Nat) : Nat :=
  max (max (wCountW P k a D) (wExpW P T k a D)) (wThrDeg P D)

theorem splitStepAMax_le_sum (k a : Nat) : splitStepAMax k a ≤ splitStepA k a := by
  unfold splitStepAMax splitStepA
  exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

theorem splitStepDMaxWith_le_sum (P T k a D : Nat) :
    splitStepDMaxWith P T k a D ≤ splitStepDWith P T k a D := by
  unfold splitStepDMaxWith splitStepDWith
  refine max_le (max_le ?_ ?_) ?_ <;> omega

/-- The split recursion with the Fejér inputs, combined by `max`. -/
def splitPairMax (seedA seedD : Nat) : Nat → Nat × Nat
  | 0 => (seedA, seedD)
  | k + 1 => if k < 2 then (seedA, seedD)
      else (splitStepAMax k (splitPairMax seedA seedD k).1,
        splitStepDMaxWith (fejerStepP k) (fejerStepT k) k
          (splitPairMax seedA seedD k).1 (splitPairMax seedA seedD k).2)

theorem splitPairMax_two (seedA seedD : Nat) : splitPairMax seedA seedD 2 = (seedA, seedD) := by
  simp [splitPairMax]

theorem splitPairMax_succ (seedA seedD : Nat) {k : Nat} (hk : 2 ≤ k) :
    splitPairMax seedA seedD (k + 1) =
      (splitStepAMax k (splitPairMax seedA seedD k).1,
        splitStepDMaxWith (fejerStepP k) (fejerStepT k) k
          (splitPairMax seedA seedD k).1 (splitPairMax seedA seedD k).2) := by
  rw [splitPairMax, if_neg (by omega)]

/-- The exact twelfth dimension fits the invariant at constant `5/2`. -/
theorem split_pair_max_twelve_half :
    1 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD 12).1 ∧
      1 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD 12).2 ∧
      2 ^ (12 + 6) * (splitPairMax splitSeedSmallA splitSeedSmallD 12).1 ≤ 2 ^ (5 * 2 ^ (12 - 1)) ∧
      (splitPairMax splitSeedSmallA splitSeedSmallD 12).2 ≤
        2 ^ (5 * 2 ^ (12 - 1) + 3 * (12 + 4) ^ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The split invariants at class constant `5/2` in every dimension `l ≥ 12`.** -/
theorem split_pair_max_half : ∀ l, 12 ≤ l →
    1 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD l).1 ∧
      1 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD l).2 ∧
      2 ^ (l + 6) * (splitPairMax splitSeedSmallA splitSeedSmallD l).1 ≤ 2 ^ (5 * 2 ^ (l - 1)) ∧
      (splitPairMax splitSeedSmallA splitSeedSmallD l).2 ≤
        2 ^ (5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2) := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => exact split_pair_max_twelve_half
  | succ k hk ih =>
    obtain ⟨ha, hDp, hAb, hDb⟩ := ih
    rw [splitPairMax_succ _ _ (by omega)]
    set a := (splitPairMax splitSeedSmallA splitSeedSmallD k).1
    set D := (splitPairMax splitSeedSmallA splitSeedSmallD k).2
    obtain ⟨h1, h2⟩ := split_step_gen ha hAb hDb ((splitStepAMax_le_sum k a).trans (splitStepA_le ha))
      ((splitStepDMaxWith_le_sum _ _ k a D).trans (splitStepDWith_le ha hDp (fejerStepP_ge k))) (fejerStepP_le k) (fejerStepT_le k)
    have he : 2 * (5 * 2 ^ (k - 1)) = 5 * 2 ^ (k + 1 - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]; ring
    refine ⟨?_, ?_, he ▸ h1, h2.trans (Nat.pow_le_pow_right (by norm_num) ?_)⟩
    · exact (show 1 ≤ sCountN k a by unfold sCountN; omega).trans (le_max_left _ _)
    · exact (show 1 ≤ wCountW (fejerStepP k) k a D by unfold wCountW; omega).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · have hs : 3 * (k + 1 + 4) ^ 2 = 3 * (k + 4) ^ 2 + 6 * k + 27 := by ring
      rw [← he, hs]
      omega

/-- **The max-split degrees beyond dimension `14`**, in closed form. -/
theorem split_pair_max_le_closed {l : Nat} (hl : 15 ≤ l) :
    (splitPairMax splitSeedSmallA splitSeedSmallD l).1 +
      (splitPairMax splitSeedSmallA splitSeedSmallD l).2 + l + 1 ≤
        2 ^ (5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2) := by
  obtain ⟨-, -, hA, hD⟩ := split_pair_max_half l (by omega)
  set a := (splitPairMax splitSeedSmallA splitSeedSmallD l).1
  set D := (splitPairMax splitSeedSmallA splitSeedSmallD l).2
  set Y := 2 ^ (5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2) with hYdef
  have ha : a ≤ Y := by
    have h1 : a ≤ 2 ^ (5 * 2 ^ (l - 1)) :=
      le_trans (Nat.le_mul_of_pos_left a (Nat.two_pow_pos _)) hA
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hl1 : l + 1 ≤ Y := by
    have h1 : l + 1 ≤ 2 ^ (l + 1) := Nat.lt_two_pow_self.le
    have h2 : l + 1 ≤ 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 := by
      have : l + 1 ≤ (l + 4) ^ 2 := by nlinarith
      omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)
  have h4 : 2 ^ (5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2) = 4 * Y := by
    rw [hYdef, pow_add]; ring
  rw [h4]
  omega

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

open BaseCase

def sPbN2 (k ac ae : Nat) : Nat := ae * (sSN k ac + 1)

def fsPbW2 (k ac Dc ae De : Nat) : Nat :=
  ae * (fejerStepP k + fsSW k ac Dc + 1) + De * (fejerStepP k + 5)

def sLN2 (k ac ae : Nat) : Nat := sBqN k ac + (sErN k ae + ae)

def fsLW2 (k ac Dc ae De : Nat) : Nat := fsBqW k ac Dc + (fsErW k ae De + fsEbW k ae De)

/-- The family exponent of the width exponent of the next two-track class. -/
def sExpN2 (k ac ae : Nat) : Nat := 1 + sLN2 k ac ae + sPbN2 k ac ae

/-- The parameter degree of the width exponent of the next two-track class. -/
def fsExpW2 (k ac Dc ae De : Nat) : Nat :=
  fsZW k ac Dc + fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 6

/-- **The width exponent of the next class from a two-track class.** -/
theorem split_exp_inv_le_fejer2 {k ac Dc ae De : Nat} (hac : 1 ≤ ac) (hDc : 1 ≤ Dc) (hae : 1 ≤ ae)
    (hDe : 1 ≤ De) {V V' : Real} (hV : 1 ≤ V)
    (hVV : V ≤ V') {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V')
    (hpV : (p : Real) ≤ V') {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPiecesFejer gamma theta k
    let tS := classBudgetW (fejerThetaOne theta gamma k) k
    let gS := section16Delta (fejerThetaOne theta gamma k)
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
            (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho *
          famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
            (clsEs (splitExp V ae De) M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (splitCnt V ac Dc tS gS M)
            (tightZeta (fejerThetaOne theta gamma k / 4)) rho)
          (pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
            (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho)
          (famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
            (clsEs (splitExp V ae De) M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ ((n : Real) + 1) ^ sExpN2 k ac ae * splitW V' theta gamma rho ^ fsExpW2 k ac Dc ae De := by
  intro M tS gS e
  obtain ⟨hw2, huw, hrw, hVw, hV'w⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, hM1, hgd, hdd⟩ := split_step_basics_fejer (k := k) hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hfacE, -⟩ := split_Qr_le_fejer (k := k) hae hDe hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hS, hS1, -, -⟩ := split_samples_le_fejer (k := k) hac hDc hV hVV hg hg1 ht ht1 hr hr1 n
  obtain ⟨hb, hb1⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  obtain ⟨-, -, hd', hd1'⟩ := section16_theta_delta_bounds_with (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  have hd : 0 < gS := hd'
  have hd1 : gS ≤ 1 := hd1'
  obtain ⟨hz0, hz1, hzi⟩ := tightZeta_fejer_inv_le_gen k hg hg1 ht ht1
  have hu0 : 0 ≤ 2 / (gamma * theta) := (div_pos two_pos (mul_pos hg ht)).le
  have hnv := classVertexNum_succ_le k
  set ν : Real := (n : Real) + 1 with hνdef
  set W := splitW V' theta gamma rho with hWdef
  set P := fejerStepP k with hPdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hV0 : 0 ≤ V := by linarith
  have hnv0 : (0 : Real) < (classVertexNum k : Real) + 1 := by
    have := Nat.cast_nonneg (α := Real) (classVertexNum k); linarith only [this]
  -- the count and the exponent controls at `ρ/8`
  have hcbGen : ∀ a D : Nat, splitCnt V a D tS gS M (rho / 8) ≤ ν ^ a * W ^ fsEbW k a D := by
    intro a D
    unfold splitCnt
    have hbase : splitW V tS gS (rho / 8) ≤ W ^ (P + 3 + 3) :=
      split_level_base_le hw2 hV0 hVw hr hrw (by norm_num) (by norm_num) hd hb hdd
    have hM10 : (0 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    have hsw0 := splitW_nonneg (V := V) (t := tS) hV0 hd hb (by positivity : (0 : Real) < rho / 8)
    have h1 := tb_pow hM10 hM1 a
    have h2 : splitW V tS gS (rho / 8) ^ D ≤ ν ^ 0 * W ^ ((P + 3 + 3) * D) := by
      rw [pow_zero, one_mul, pow_mul]
      exact pow_le_pow_left₀ hsw0 hbase D
    have h12 := tb_mul hν hW1 (pow_nonneg hM10 _) (pow_nonneg hsw0 _) h1 h2
    exact h12.trans (tb_mono hν hW1 (by omega) (le_of_eq (by unfold fsEbW; rw [← hPdef]; ring)))
  have hcb1Gen : ∀ a D : Nat, 1 ≤ splitCnt V a D tS gS M (rho / 8) := by
    intro a D
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hd hd1 hb hb1 (by positivity : (0 : Real) < rho / 8)
      (by linarith only [hr1])
    have hM1' : (1 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1') (one_le_pow₀ (by linarith))
  have hcb := hcbGen ac Dc
  have hcb1 := hcb1Gen ac Dc
  have hEb0 : 0 < splitExp V ae De tS gS M (rho / 8) := by
    show 0 < (splitCnt V ae De tS gS M (rho / 8))⁻¹
    exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hcb1Gen ae De))
  have hEbi : (splitExp V ae De tS gS M (rho / 8))⁻¹ ≤ ν ^ ae * W ^ fsEbW k ae De := by
    show ((splitCnt V ae De tS gS M (rho / 8))⁻¹)⁻¹ ≤ _
    rw [inv_inv]; exact hcbGen ae De
  -- the remainder exponent at `ρ/8`, from the exponent track
  have hfac' : splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) ≤
      ν ^ ae * W ^ fsStepY k ae De := (le_max_left _ _).trans hfacE
  have hscale : 0 < rho / 8 / ((classVertexNum k : Real) + 1) :=
    div_pos (div_pos hr (by norm_num)) hnv0
  have hcr1 : 1 ≤ splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) := by
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hg hg1 hb hb1 hscale (by
      rw [div_le_one hnv0]; have := Nat.cast_nonneg (α := Real) (classVertexNum k)
      linarith only [this, hr1])
    have hM1' : (1 : Real) ≤ (M : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) M; linarith
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hM1') (one_le_pow₀ (by linarith))
  set cr := splitCnt V ae De tS gamma M (rho / 8 / ((classVertexNum k : Real) + 1)) with hcrdef
  have hEr : clsEr (splitExp V ae De) k M tS gamma (rho / 8) =
      (cr⁻¹ / 16) ^ (classVertexNum k + 1) := by
    unfold clsEr
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  have hEr0 : 0 < clsEr (splitExp V ae De) k M tS gamma (rho / 8) := by
    rw [hEr]; exact pow_pos (div_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hcr1)) (by norm_num)) _
  have hEri : (clsEr (splitExp V ae De) k M tS gamma (rho / 8))⁻¹ ≤ ν ^ sErN k ae * W ^ fsErW k ae De := by
    rw [hEr, ← inv_pow, inv_div, div_inv_eq_mul]
    have h16 : 16 * cr ≤ ν ^ ae * W ^ (4 + fsStepY k ae De) :=
      tb_const_mul hν hw2 (by norm_num) (by norm_num) (le_trans zero_le_one hcr1) hfac'
    have h16' : 16 * cr ≤ ν ^ ae * W ^ (fsStepY k ae De + 4) := by rw [add_comm]; exact h16
    have hone : (1 : Real) ≤ ν ^ ae * W ^ (fsStepY k ae De + 4) := tb_one_le hν hW1
    calc (16 * cr) ^ (classVertexNum k + 1) ≤ (ν ^ ae * W ^ (fsStepY k ae De + 4)) ^ (classVertexNum k + 1) :=
          pow_le_pow_left₀ (by linarith) h16' _
      _ ≤ (ν ^ ae * W ^ (fsStepY k ae De + 4)) ^ (2 ^ k) := pow_le_pow_right₀ hone hnv
      _ = ν ^ sErN k ae * W ^ fsErW k ae De := by
          unfold sErN fsErW; rw [mul_pow, ← pow_mul, ← pow_mul]
  -- the divisor, from the count track
  set q := ⌊splitCnt V ac Dc tS gS M (rho / 8)⌋₊ with hqdef
  have hq : (q : Real) ≤ ν ^ ac * W ^ fsEbW k ac Dc :=
    (Nat.floor_le (le_trans zero_le_one hcb1)).trans hcb
  have hq1 : ((q + 1 : Nat) : Real) ≤ ν ^ ac * W ^ (fsEbW k ac Dc + 1) := by
    push_cast; exact tb_add_one hν hw2 hq
  have hBq : familyWidthDivisor k p q ≤ ν ^ sBqN k ac * W ^ fsBqW k ac Dc := by
    unfold familyWidthDivisor
    have hpow : (((q + 1) ^ (2 * 2 ^ (k + 1)) : Nat) : Real) ≤
        ν ^ (ac * 2 ^ (k + 2)) * W ^ ((fsEbW k ac Dc + 1) * 2 ^ (k + 2)) := by
      rw [Nat.cast_pow, show 2 * 2 ^ (k + 1) = 2 ^ (k + 2) by rw [pow_succ 2 (k + 1)]; ring]
      exact tb_pow (Nat.cast_nonneg _) hq1 _
    have hpw : ((p : Nat) : Real) ≤ ν ^ 0 * W ^ 1 := by
      rw [pow_zero, one_mul, pow_one]; exact hpV.trans hV'w
    have h1 := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hpw hpow
    rw [← Nat.cast_mul] at h1
    have h2 := tb_const_mul (c := (2 : Real)) (j := 1) hν hw2 (by norm_num) (by norm_num)
      (Nat.cast_nonneg _) h1
    have h3 := tb_const_mul (c := (4 : Real)) (j := 2) hν hw2 (by norm_num) (by norm_num)
      (by positivity) h2
    push_cast at h3 ⊢
    refine h3.trans (tb_mono hν hW1 (by unfold sBqN; omega) ?_)
    unfold fsBqW
    omega
  have hBq0 : 0 < familyWidthDivisor k p q := familyWidthDivisor_pos hp q
  -- the line exponent
  set L := pieceLineExponent (familyWidthDivisor k p) (splitCnt V ac Dc tS gS M)
    (splitExp V ae De tS gS M) (clsEr (splitExp V ae De) k M tS gamma) rho with hLdef
  have hL0 : 0 < L := by
    rw [hLdef]; unfold pieceLineExponent
    exact div_pos (mul_pos hEr0 hEb0) hBq0
  have hLi : L⁻¹ ≤ ν ^ sLN2 k ac ae * W ^ fsLW2 k ac Dc ae De := by
    rw [hLdef]; unfold pieceLineExponent
    rw [inv_div, div_eq_mul_inv, mul_inv, ← hqdef]
    have h1 := tb_mul hν hW1 (inv_pos.mpr hEr0).le (inv_pos.mpr hEb0).le hEri hEbi
    exact tb_mul hν hW1 hBq0.le (by positivity) hBq h1
  -- the slice exponent: samples from the count track, slices from the exponent track
  set S := famPieceSamples (clsQr (splitCnt V ac Dc) k M tS gamma) M rho with hSdef
  have hPbE : splitCnt V ae De tS gamma (M * S) (rho / 4) ≤ ν ^ sPbN2 k ac ae * W ^ fsPbW2 k ac Dc ae De := by
    have hMS : ((M * S : Nat) : Real) + 1 ≤ ν ^ (1 + sSN k ac) * W ^ (P + fsSW k ac Dc + 1) := by
      have h := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hM hS
      rw [← Nat.cast_mul] at h
      exact tb_add_one hν hw2 h
    have hbase : splitW V tS gamma (rho / 4) ≤ W ^ (P + 2 + 3) :=
      split_level_base_le hw2 hV0 hVw hr hrw (by norm_num) (by norm_num) hg hb hgd
    have hMS0 : (0 : Real) ≤ ((M * S : Nat) : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (M * S); linarith
    have hsw0 := splitW_nonneg (V := V) (t := tS) hV0 hg hb (by positivity : (0 : Real) < rho / 4)
    unfold splitCnt
    have h1 := tb_pow hMS0 hMS ae
    have h2 : splitW V tS gamma (rho / 4) ^ De ≤ ν ^ 0 * W ^ ((P + 2 + 3) * De) := by
      rw [pow_zero, one_mul, pow_mul]
      exact pow_le_pow_left₀ hsw0 hbase De
    have h12 := tb_mul hν hW1 (pow_nonneg hMS0 _) (pow_nonneg hsw0 _) h1 h2
    push_cast at h12 ⊢
    refine h12.trans (tb_mono hν hW1 (le_of_eq (by unfold sPbN2; ring))
      (le_of_eq (by unfold fsPbW2; rw [← hPdef]; ring)))
  have hPbE1 : 1 ≤ splitCnt V ae De tS gamma (M * S) (rho / 4) := by
    unfold splitCnt
    obtain ⟨h2, -, -, -⟩ := splitW_facts hV hg hg1 hb hb1
      (by positivity : (0 : Real) < rho / 4) (by linarith only [hr1])
    have hMS1 : (1 : Real) ≤ ((M * S : Nat) : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) (M * S); linarith
    push_cast at hMS1 ⊢
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hMS1) (one_le_pow₀ (by linarith))
  set Sl := famPieceSliceExponent (clsQr (splitCnt V ac Dc) k M tS gamma)
    (clsEs (splitExp V ae De) M tS gamma) M rho with hSldef
  have hSlval : Sl = (splitCnt V ae De tS gamma (M * S) (rho / 4))⁻¹ := by
    rw [hSldef]
    unfold famPieceSliceExponent clsEs
    rw [← hSdef, abs_of_pos (by positivity : (0 : Real) < rho / 4)]
    rfl
  have hSl0 : 0 < Sl := by rw [hSlval]; exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one hPbE1)
  have hSl1 : Sl ≤ 1 := by rw [hSlval]; exact inv_le_one_of_one_le₀ hPbE1
  have hSli : Sl⁻¹ ≤ ν ^ sPbN2 k ac ae * W ^ fsPbW2 k ac Dc ae De := by
    rw [hSlval, inv_inv]; exact hPbE
  -- the width scale, from the count track
  have hA1 : 1 ≤ familyWidthPrefactor K q := by
    unfold familyWidthPrefactor
    have : (1 : Real) ≤ ((K * (q + 1) : Nat) : Real) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    linarith only [this]
  have hA : familyWidthPrefactor K q ≤ ν ^ ac * W ^ (2 + (1 + (fsEbW k ac Dc + 1))) := by
    unfold familyWidthPrefactor
    have hKw : ((K : Nat) : Real) ≤ ν ^ 0 * W ^ 1 := by
      rw [pow_zero, one_mul, pow_one]; exact hKV.trans hV'w
    have h1 := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hKw hq1
    rw [← Nat.cast_mul, zero_add] at h1
    exact tb_const_mul (c := (4 : Real)) (j := 2) hν hw2 (by norm_num) (by norm_num)
      (Nat.cast_nonneg _) h1
  set z := pieceWidthScale (familyWidthPrefactor K) (splitCnt V ac Dc tS gS M)
    (tightZeta (fejerThetaOne theta gamma k / 4)) rho with hzdef
  have hzval : z = tightZeta (fejerThetaOne theta gamma k / 4) / familyWidthPrefactor K q := by rw [hzdef]; rfl
  have hzpos : 0 < z := by rw [hzval]; exact div_pos hz0 (lt_of_lt_of_le zero_lt_one hA1)
  have hzle : z ≤ 1 := by
    rw [hzval, div_le_one (lt_of_lt_of_le zero_lt_one hA1)]; exact hz1.trans hA1
  set Λ := (ac : Real) * ν + ((fsEbW k ac Dc + 4 : Nat) : Real) * W + W ^ fejerStepT k with hΛdef
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; positivity
  have hzinv : z⁻¹ ≤ Real.exp Λ := by
    rw [hzval, inv_div, div_eq_mul_inv]
    have hAexp : familyWidthPrefactor K q ≤ Real.exp ((ac : Real) * ν + ((fsEbW k ac Dc + 4 : Nat) : Real) * W) := by
      have h1 : ν ^ ac ≤ Real.exp ((ac : Real) * ν) := pow_le_exp_mul (by linarith) ac
      have h2 : W ^ (fsEbW k ac Dc + 4) ≤ Real.exp (((fsEbW k ac Dc + 4 : Nat) : Real) * W) :=
        pow_le_exp_mul (by linarith) _
      rw [Real.exp_add]
      refine hA.trans ?_
      rw [show 2 + (1 + (fsEbW k ac Dc + 1)) = fsEbW k ac Dc + 4 by ring]
      exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    have hze : (tightZeta (fejerThetaOne theta gamma k / 4))⁻¹ ≤ Real.exp (W ^ fejerStepT k) :=
      hzi.trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ hu0 huw _))
    rw [hΛdef, Real.exp_add]
    exact mul_le_mul hAexp hze (inv_pos.mpr hz0).le (Real.exp_pos _).le
  have hΛle : Λ ≤ ν * W ^ fsZW k ac Dc := by
    rw [hΛdef]
    have hZ : fsZW k ac Dc = fejerStepT k + ac + fsEbW k ac Dc + 7 := rfl
    set X := W ^ (fejerStepT k + ac + fsEbW k ac Dc + 5) with hXdef
    have hX0 : 0 ≤ X := pow_nonneg hW0 _
    have hνX : X ≤ ν * X := le_mul_of_one_le_left hX0 hν
    have hν0 : 0 ≤ ν := le_trans zero_le_one hν
    have h1 : (ac : Real) * ν ≤ ν * X := by
      have ha' := nat_le_two_pow_real ac hw2
      have hle : W ^ ac ≤ X := pow_le_pow_right₀ hW1 (by omega)
      calc (ac : Real) * ν ≤ W ^ ac * ν := mul_le_mul_of_nonneg_right ha' hν0
        _ ≤ X * ν := mul_le_mul_of_nonneg_right hle hν0
        _ = ν * X := mul_comm _ _
    have h2 : ((fsEbW k ac Dc + 4 : Nat) : Real) * W ≤ ν * X := by
      have hc := nat_le_two_pow_real (fsEbW k ac Dc + 4) hw2
      have hle : W ^ (fsEbW k ac Dc + 4) * W ≤ X := by
        rw [← pow_succ]; exact pow_le_pow_right₀ hW1 (by omega)
      calc ((fsEbW k ac Dc + 4 : Nat) : Real) * W ≤ W ^ (fsEbW k ac Dc + 4) * W :=
            mul_le_mul_of_nonneg_right hc hW0
        _ ≤ X := hle
        _ ≤ ν * X := hνX
    have h3 : W ^ fejerStepT k ≤ ν * X := by
      have hle : W ^ fejerStepT k ≤ X := pow_le_pow_right₀ hW1 (by omega)
      exact hle.trans hνX
    have h3W : (3 : Real) ≤ W ^ 2 := by nlinarith only [hw2]
    have hpos : 0 ≤ ν * X := mul_nonneg hν0 hX0
    rw [hZ, show fejerStepT k + ac + fsEbW k ac Dc + 7 = (fejerStepT k + ac + fsEbW k ac Dc + 5) + 2 by ring, pow_add,
      ← hXdef]
    calc (ac : Real) * ν + ((fsEbW k ac Dc + 4 : Nat) : Real) * W + W ^ fejerStepT k ≤ 3 * (ν * X) := by
          linarith
      _ ≤ W ^ 2 * (ν * X) := mul_le_mul_of_nonneg_right h3W hpos
      _ = ν * (X * W ^ 2) := by ring
  -- the cap
  set R := ν ^ (sLN2 k ac ae + sPbN2 k ac ae) *
    W ^ (fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 2) with hRdef
  have hR1 : 1 ≤ R := tb_one_le hν hW1
  have hLR : L⁻¹ ≤ R := hLi.trans (tb_mono hν hW1 (by omega) (by omega))
  have hLSR : (L * Sl / 4)⁻¹ ≤ R := by
    rw [show (L * Sl / 4)⁻¹ = 4 * (L⁻¹ * Sl⁻¹) by field_simp]
    have h := tb_mul hν hW1 (inv_pos.mpr hL0).le (inv_pos.mpr hSl0).le hLi hSli
    have h4 := tb_const_mul (c := (4 : Real)) (j := 2) hν hw2 (by norm_num) (by norm_num)
      (mul_nonneg (inv_pos.mpr hL0).le (inv_pos.mpr hSl0).le) h
    exact h4.trans (tb_mono hν hW1 le_rfl (by omega))
  have hcap := capped_rounded_inv_le_real hL0 hSl0 hSl1 hzpos hzle hΛ0 hzinv hR1 hLR hLSR
  refine ⟨section16CappedWidthExponent_pos (div_pos (mul_pos hL0 hSl0) (by norm_num)), ?_⟩
  refine hcap.trans ?_
  have hW4 : (14 : Real) ≤ W ^ 4 := by
    calc (14 : Real) ≤ 2 ^ 4 := by norm_num
      _ ≤ W ^ 4 := pow_le_pow_left₀ (by norm_num) hw2 4
  have hνW : 1 ≤ ν * W ^ fsZW k ac Dc := one_le_mul_of_one_le_of_one_le hν (one_le_pow₀ hW1)
  have hfront : 2 * (6 + Λ) ≤ ν * W ^ (fsZW k ac Dc + 4) := by
    rw [pow_add]
    have : 2 * (6 + Λ) ≤ 14 * (ν * W ^ fsZW k ac Dc) := by linarith
    calc 2 * (6 + Λ) ≤ 14 * (ν * W ^ fsZW k ac Dc) := this
      _ ≤ W ^ 4 * (ν * W ^ fsZW k ac Dc) := mul_le_mul_of_nonneg_right hW4 (le_trans zero_le_one hνW)
      _ = ν * (W ^ fsZW k ac Dc * W ^ 4) := by ring
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  calc 2 * ((6 + Λ) * R) = (2 * (6 + Λ)) * R := by ring
    _ ≤ (ν * W ^ (fsZW k ac Dc + 4)) * R := mul_le_mul_of_nonneg_right hfront hR0
    _ = ν ^ (1 + (sLN2 k ac ae + sPbN2 k ac ae)) *
          W ^ ((fsZW k ac Dc + 4) + (fsLW2 k ac Dc ae De + fsPbW2 k ac Dc ae De + 2)) := by
        rw [hRdef]; ring
    _ ≤ ν ^ sExpN2 k ac ae * W ^ fsExpW2 k ac Dc ae De :=
        tb_mono hν hW1 (by unfold sExpN2; omega) (by unfold fsExpW2; omega)

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

open BaseCase

/-- **A two-track split class.** -/
abbrev SplitUniformClass2 (k : Nat) (V : Real) (ac Dc ae De : Nat) :=
  UniformClassWith k (fun theta gamma => (V * (2 / (gamma * theta))) ^ Dc)
    (fun theta gamma n rho => ((n : Real) + 1) ^ ac * splitW V theta gamma rho ^ Dc)
    (fun theta gamma n rho => (((n : Real) + 1) ^ ae * splitW V theta gamma rho ^ De)⁻¹)

/-- **A two-track class is a split class** at `(max ac ae, max Dc De)`. -/
def SplitUniformClass2.toSplit {k : Nat} {V : Real} {ac Dc ae De : Nat}
    (C : SplitUniformClass2 k V ac Dc ae De) (hV : 1 ≤ V) :
    SplitUniformClass k V (max ac ae) (max Dc De) where
  U := C.U
  mono := C.mono
  empty := C.empty
  decomp := by
    intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    refine C.decomp theta gamma ht ht1 hg hg1 N (le_trans ?_ hN) Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le hV (le_trans (by norm_num) hu2)
    exact pow_le_pow_right₀ hVu (le_max_left _ _)
  cover := by
    intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    refine (C.cover theta gamma ht ht1 hg hg1 N n Gamma hU).weaken ?_ ?_ ?_
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact tb_mono hν (by linarith) (le_max_left _ _) (le_max_left _ _)
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have : (0 : Real) < splitW V theta gamma rho := by linarith
      positivity
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      have hW0 : (0 : Real) < splitW V theta gamma rho := by linarith
      refine inv_anti₀ (by positivity) ?_
      exact tb_mono hν (by linarith) (le_max_right _ _) (le_max_right _ _)

/-- **The two-track split step.** -/
theorem splitUniformClass2_succ_fejer {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V)
    {ac Dc ae De : Nat} (hac : 1 ≤ ac) (hDc : 1 ≤ Dc) (hae : 1 ≤ ae) (hDe : 1 ≤ De)
    (C : SplitUniformClass2 k V ac Dc ae De) {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    Nonempty (SplitUniformClass2 (k + 1) V' (sCountN k ac)
      (max (fsCountW k ac Dc) (fejerStepThrDeg k Dc)) (sExpN2 k ac ae) (fsExpW2 k ac Dc ae De)) := by
  classical
  obtain ⟨hCnt, -, hCntMono, -⟩ := splitCnt_controls hV ac Dc
  obtain ⟨-, hExp, -, hExpAnti⟩ := splitCnt_controls hV ae De
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (classPiecesFejer gamma theta k) → StepPieceFejer C N theta gamma,
        Gamma ⊆ stepPieceFejerGraphs C P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => ClassPiece.empty C _ _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V' * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le (hV.trans hVV) (le_trans (by norm_num) hu2)
    have hN' : classStepThrFejer (fun theta gamma => (V * (2 / (gamma * theta))) ^ Dc) theta gamma k ≤ N := by
      rw [← classStepThresholdFejer_eq]
      refine (step_thr_le_fejer hk hV hVV hg hg1 ht ht1).trans (le_trans ?_ hN)
      exact pow_le_pow_right₀ hVu (le_max_right _ _)
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp_fejer C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover_gen_fejer C hk hCnt hExp hCntMono hExpAnti (familyWidthPrefactor_pos hK)
      (familyWidthDivisor_pos hp) hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      have hc := split_count_le_fejer (k := k) hac hDc hV hVV hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact hc.trans (tb_mono hν (by linarith) le_rfl (le_max_left _ _))
    · intro rho hr hr1
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (tb_one_le hν (by linarith)))
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := split_exp_inv_le_fejer2 (k := k) hac hDc hae hDe hV hVV hK hp hKV hpV
        hg hg1 ht ht1 hr hr1 n
      obtain ⟨hw2, -, -, -, -⟩ := split_w_facts hV hVV hg hg1 ht ht1 hr hr1
      have hν : (1 : Real) ≤ (n : Real) + 1 := by
        have := Nat.cast_nonneg (α := Real) n; linarith
      have h2 := inv_anti₀ (inv_pos.mpr he0) hei
      rw [inv_inv] at h2
      exact h2

/-- One two-track step on `((ac, Dc), (ae, De))`. -/
def splitQuadStep (k : Nat) (x : (Nat × Nat) × (Nat × Nat)) : (Nat × Nat) × (Nat × Nat) :=
  ((sCountN k x.1.1, max (fsCountW k x.1.1 x.1.2) (fejerStepThrDeg k x.1.2)),
    (sExpN2 k x.1.1 x.2.1, fsExpW2 k x.1.1 x.1.2 x.2.1 x.2.2))

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

open BaseCase

theorem polyPieceFaceCountW_fejer_le_tight {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma : Real) ≤
      (2 / (gamma * theta)) ^ (10002 * (2 ^ 23 + 1) : Nat) := by
  obtain ⟨hu2, -, h2g, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, hb1⟩ := polyPieceBudgetW_fejer_pos_le hg hg1 ht ht1
  have hbinv := polyPieceBudgetW_fejer_inv_le_power hg hg1 ht ht1
  have hBF := section16BaseFamilyBound_le_power hg hg1 hb hb1
  unfold polyPieceFaceCountW
  set b := polyPieceBudgetW (fejerThetaOne theta gamma 1)
  set u := 2 / (gamma * theta) with hu
  clear_value u b
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  have hbase : 2 / (gamma * b) ≤ u ^ ((2 : Nat) ^ 23 + 1) := by
    rw [show 2 / (gamma * b) = 2 / gamma * b⁻¹ by field_simp]
    rw [pow_succ, mul_comm (u ^ _) u]
    exact mul_le_mul h2g hbinv (inv_pos.mpr hb).le hupos.le
  refine hBF.trans ?_
  calc (2 / (gamma * b)) ^ (10002 : Nat)
      ≤ (u ^ ((2 : Nat) ^ 23 + 1)) ^ (10002 : Nat) :=
        pow_le_pow_left₀ (div_pos (by norm_num) (mul_pos hg hb)).le hbase _
    _ = u ^ ((2 ^ 23 + 1) * 10002) := (pow_mul _ _ _).symm
    _ = u ^ (10002 * (2 ^ 23 + 1) : Nat) := by rw [mul_comm]

theorem uniTwoFejerCount_le_split_tight {V : Real} (hV : 1 ≤ V) {gamma theta rho : Real} (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    uniTwoFejerCount theta gamma (n * polyTwoFejerPieces gamma theta) rho ≤
      ((n : Real) + 1) ^ 11 * splitW V theta gamma rho ^ ((2 : Nat) ^ 39) := by
  obtain ⟨hW2, -, hrW, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
  obtain ⟨hM, -, -⟩ := two_split_basics hV hg hg1 ht ht1 hr hr1 n
  have hqf : (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma : Real) ≤
      ((n : Real) + 1) ^ 0 * splitW V theta gamma rho ^ (10002 * (2 ^ 23 + 1) : Nat) := by
    obtain ⟨-, hvW, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hu0 : (0 : Real) ≤ 2 / (gamma * theta) := le_trans (by norm_num) hu2
    rw [pow_zero, one_mul]
    exact (polyPieceFaceCountW_fejer_le_tight hg hg1 ht ht1).trans (pow_le_pow_left₀ hu0 hvW _)
  set W := splitW V theta gamma rho with hWdef
  set ν : Real := (n : Real) + 1 with hνdef
  set M := n * polyTwoFejerPieces gamma theta with hMdef
  set qf := polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma with hqfdef
  clear_value W
  have hν : 1 ≤ ν := by rw [hνdef]; have := Nat.cast_nonneg (α := Real) n; linarith
  have hW1 : 1 ≤ W := by linarith
  have hW0 : 0 ≤ W := by linarith
  have hν0 : 0 ≤ ν := by linarith
  -- the remainder count
  have hMq := affine_le_tb hν hW2 hM hqf
  have hQr : ∀ t, famTwoQr M qf t ≤ ν ^ 1 * W ^ (4 + ((2 : Nat) ^ 24 + (10002 * (2 ^ 23 + 1) : Nat) + 1)) := by
    intro t
    unfold famTwoQr
    have h9 : ((9 * (M * qf + 1) : Nat) : Real) ≤ ν ^ 1 * W ^ (4 + ((2 : Nat) ^ 24 + (10002 * (2 ^ 23 + 1) : Nat) + 1)) := by
      rw [Nat.cast_mul]
      exact tb_const_mul hν hW2 (by norm_num) (by norm_num) (Nat.cast_nonneg _) hMq
    apply max_le
    · refine le_trans ?_ h9
      exact_mod_cast Nat.mul_le_mul_right _ (by norm_num : 3 ≤ 9)
    · simpa using h9
  -- the samples
  set Q := (4 : Nat) + ((2 : Nat) ^ 24 + (10002 * (2 ^ 23 + 1) : Nat) + 1) with hQdef
  have hS : (famPieceSamples (famTwoQr M qf) M rho : Real) ≤
      ν ^ (1 + 1) * W ^ (5 + (Q + (2 : Nat) ^ 24 + 1) + 1) := by
    unfold famPieceSamples
    have hQ1 : max 1 (famTwoQr M qf (rho / 8)) ≤ ν ^ 1 * W ^ Q :=
      max_le (tb_one_le hν hW1) (hQr _)
    have hM1 : ((max 1 M : Nat) : Real) ≤ ν ^ 1 * W ^ ((2 : Nat) ^ 24) := by
      rw [Nat.cast_max, Nat.cast_one]; exact max_le (tb_one_le hν hW1) hM
    have hprod := tb_mul hν hW1 (le_trans zero_le_one (le_max_left _ _)) (Nat.cast_nonneg _) hQ1 hM1
    have hρ : rho⁻¹ ≤ ν ^ 0 * W ^ 1 := by rw [pow_zero, one_mul, pow_one]; exact hrW
    have hprod2 := tb_mul hν hW1 (by positivity) (inv_pos.mpr hr).le hprod hρ
    have hx0 : 0 ≤ 6 * max 1 (famTwoQr M qf (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4) := by
      have : (0 : Real) ≤ max 1 (famTwoQr M qf (rho / 8)) := le_trans zero_le_one (le_max_left _ _)
      positivity
    have hval : 6 * max 1 (famTwoQr M qf (rho / 8)) * ((max 1 M : Nat) : Real) / (rho / 4) =
        24 * (max 1 (famTwoQr M qf (rho / 8)) * ((max 1 M : Nat) : Real) * rho⁻¹) := by
      field_simp; ring
    have h24 := tb_const_mul (c := (24 : Real)) (j := 5) hν hW2 (by norm_num) (by norm_num)
      (by have : (0 : Real) ≤ max 1 (famTwoQr M qf (rho / 8)) := le_trans zero_le_one (le_max_left _ _)
          positivity) hprod2
    have hceil := (Nat.ceil_lt_add_one hx0).le
    rw [hval] at hceil ⊢
    rw [Nat.add_zero] at h24
    exact hceil.trans (tb_add_one hν hW2 h24)
  set S := famPieceSamples (famTwoQr M qf) M rho with hSdef
  set SB := 5 + (Q + (2 : Nat) ^ 24 + 1) + 1 with hSBdef
  -- the slice count
  have hSq : ((S : Real) * qf) ≤ ν ^ 2 * W ^ (SB + (10002 * (2 ^ 23 + 1) : Nat)) := by
    have h := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hS hqf
    simpa using h
  have hPb : famTwoPb M qf S (rho / 4) ≤ ν ^ 3 * W ^ (2 + ((2 : Nat) ^ 24 + (SB + (10002 * (2 ^ 23 + 1) : Nat))) + 1) := by
    unfold famTwoPb
    have h1 := tb_mul hν hW1 (Nat.cast_nonneg _) (by positivity) hM hSq
    have h2 : ((M * (S * qf) + 1 : Nat) : Real) ≤ ν ^ (1 + 2) * W ^ ((2 : Nat) ^ 24 + (SB + (10002 * (2 ^ 23 + 1) : Nat)) + 1) := by
      push_cast
      have : (M : Real) * ((S : Real) * qf) + 1 ≤ ν ^ (1 + 2) * W ^ ((2 : Nat) ^ 24 + (SB + (10002 * (2 ^ 23 + 1) : Nat)) + 1) :=
        tb_add_one hν hW2 h1
      exact this
    rw [Nat.cast_mul, show ν ^ 3 * W ^ (2 + ((2 : Nat) ^ 24 + (SB + (10002 * (2 ^ 23 + 1) : Nat))) + 1) =
      ν ^ (1 + 2) * W ^ (2 + ((2 : Nat) ^ 24 + (SB + (10002 * (2 ^ 23 + 1) : Nat)) + 1)) by ring_nf]
    exact tb_const_mul hν hW2 (by norm_num) (by norm_num) (Nat.cast_nonneg _) h2
  set PB := 2 + ((2 : Nat) ^ 24 + (SB + (10002 * (2 ^ 23 + 1) : Nat))) + 1 with hPBdef
  have hP0 : 0 ≤ famTwoPb M qf S (rho / 4) := by unfold famTwoPb; exact Nat.cast_nonneg _
  have hch : ((S.choose 2 : Nat) : Real) ≤ ν ^ 4 * W ^ (2 * SB) := by
    have h1 : S.choose 2 ≤ S * S := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    have h2 := tb_mul hν hW1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hS hS
    calc ((S.choose 2 : Nat) : Real) ≤ (S : Real) * S := by exact_mod_cast h1
      _ ≤ ν ^ (1 + 1 + (1 + 1)) * W ^ (SB + SB) := h2
      _ = ν ^ 4 * W ^ (2 * SB) := by ring_nf
  -- the graph bound
  have hG : famPieceGraphBound (famTwoQr M qf) (famTwoPb M qf) M rho ≤
      ν ^ 11 * W ^ ((2 : Nat) ^ 24 + (2 * SB + PB + PB)) := by
    unfold famPieceGraphBound
    have hmax : max (famTwoPb M qf S (rho / 4))
        (((S.choose 2 : Nat) : Real) * famTwoPb M qf S (rho / 4) * famTwoPb M qf S (rho / 4)) ≤
        ν ^ 10 * W ^ (2 * SB + PB + PB) := by
      apply max_le
      · exact hPb.trans (tb_mono hν hW1 (by norm_num) (by omega))
      · have h := tb_mul hν hW1 (by positivity) hP0 (tb_mul hν hW1 (Nat.cast_nonneg _) hP0 hch hPb) hPb
        exact h.trans (le_of_eq (by ring_nf))
    have h := tb_mul hν hW1 (Nat.cast_nonneg _) (le_trans hP0 (le_max_left _ _)) hM hmax
    exact h.trans (le_of_eq (by ring_nf))
  unfold uniTwoFejerCount
  refine max_le (hG.trans (tb_mono hν hW1 le_rfl ?_)) ?_
  · rw [hPBdef, hSBdef, hQdef]; norm_num
  · have h9 : ((3 ^ (1 + 1) * M : Nat) : Real) ≤ ν ^ 1 * W ^ (4 + (2 : Nat) ^ 24) := by
      rw [Nat.cast_mul]
      exact tb_const_mul hν hW2 (by norm_num) (by norm_num) (Nat.cast_nonneg _) hM
    exact h9.trans (tb_mono hν hW1 (by norm_num) (by norm_num))

/-- **Dimension two as a two-track class at the tight count**: count `(11, 2^39)`, exponent `(29, 2^46)`. -/
theorem splitUniformClass2_two_tight {K1 p1 : Nat} (hK1 : 1 ≤ K1) (hp1 : 0 < p1)
    (hlemma6 : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {V : Real} (hV : 1 ≤ V) (hKV : (K1 : Real) ≤ V) (hpV : (p1 : Real) ≤ V) :
    Nonempty (SplitUniformClass2 2 V 11 ((2 : Nat) ^ 39) 29 ((2 : Nat) ^ 46)) := by
  classical
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (polyTwoFejerPieces gamma theta) → PolyPieceTwoFejer N theta gamma,
        Gamma ⊆ polyPieceTwoFejerGraphs P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => PolyPieceTwoData.empty _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hVu : 1 ≤ V * (2 / (gamma * theta)) :=
      one_le_mul_of_one_le_of_one_le hV (le_trans (by norm_num) hu2)
    have hthr : polyTwoFejerThreshold theta gamma ≤ N := by
      refine (polyTwoFejerThreshold_le_power hg hg1 ht ht1).trans (le_trans ?_ hN)
      refine (pow_le_pow_left₀ (by linarith only [hu2])
        (le_mul_of_one_le_left (by linarith only [hu2]) hV) _).trans ?_
      exact pow_le_pow_right₀ hVu (Nat.pow_le_pow_right (by norm_num) (by norm_num))
    obtain ⟨J, hJ, P, hP⟩ := section16_poly_piece_decomposition_two_fejer ht ht1 hg hg1 hthr Gamma
      hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have hcov := section16_uniform_cover_two_fejer (familyWidthPrefactor_pos hK1)
      (familyWidthDivisor_pos hp1) hlemma6 ht ht1 hg hg1 Gamma (fun _ => Finset.univ) P
      (fun i => by rw [restrictRelation_univ]; exact hP i)
    have hsub : Finset.univ.biUnion Gamma ⊆
        Finset.univ.biUnion fun i => restrictRelation (Gamma i) Finset.univ := by
      simp only [restrictRelation_univ]; exact le_rfl
    have hν : (1 : Real) ≤ (n : Real) + 1 := by
      have := Nat.cast_nonneg (α := Real) n; linarith only [this]
    refine (hcov.subset hsub).weaken ?_ ?_ ?_
    · intro rho hr hr1
      exact uniTwoFejerCount_le_split_tight hV hg hg1 ht ht1 hr hr1 n
    · intro rho hr hr1
      obtain ⟨hW2, -, -, -⟩ := splitW_facts hV hg hg1 ht ht1 hr hr1
      have : (0 : Real) < splitW V theta gamma rho := by linarith only [hW2]
      positivity
    · intro rho hr hr1
      have h := uniTwoFejerExp_inv_le_split hV (by omega : 0 < K1) hp1 hKV hpV hg hg1 ht ht1 hr hr1 n
      have h0 := uniTwoFejerExp_pos (A := familyWidthPrefactor K1) (Bq := familyWidthDivisor 1 p1)
        (familyWidthDivisor_pos (k := 1) hp1)
        (theta := theta) (gamma := gamma) (n * polyTwoFejerPieces gamma theta) hr
      have := inv_anti₀ (inv_pos.mpr h0) h
      rwa [inv_inv] at this

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

open BaseCase

/-- The two-track recursion from the dimension-two seed. -/
def splitQuad3 : Nat → (Nat × Nat) × (Nat × Nat)
  | 0 => ((11, 2 ^ 39), (29, 2 ^ 46))
  | k + 1 => if k < 2 then ((11, 2 ^ 39), (29, 2 ^ 46)) else splitQuadStep k (splitQuad3 k)

theorem splitQuad3_two : splitQuad3 2 = ((11, 2 ^ 39), (29, 2 ^ 46)) := by simp [splitQuad3]

theorem splitQuad3_succ {k : Nat} (hk : 2 ≤ k) : splitQuad3 (k + 1) = splitQuadStep k (splitQuad3 k) := by
  rw [splitQuad3, if_neg (by omega)]

/-- **The two-track degrees stay below the `max` pairs.** -/
theorem split_quad3_le_max : ∀ l, 2 ≤ l →
    1 ≤ (splitQuad3 l).1.1 ∧ 1 ≤ (splitQuad3 l).1.2 ∧ 1 ≤ (splitQuad3 l).2.1 ∧ 1 ≤ (splitQuad3 l).2.2 ∧
      (splitQuad3 l).1.1 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD l).1 ∧
      (splitQuad3 l).1.2 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD l).2 ∧
      (splitQuad3 l).2.1 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD l).1 ∧
      (splitQuad3 l).2.2 ≤ (splitPairMax splitSeedSmallA splitSeedSmallD l).2 := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base =>
    rw [splitQuad3_two, splitPairMax_two]
    unfold splitSeedSmallA splitSeedSmallD
    refine ⟨by norm_num, Nat.one_le_two_pow, by norm_num, Nat.one_le_two_pow, by norm_num,
      Nat.pow_le_pow_right (by norm_num) (by norm_num), by norm_num,
      Nat.pow_le_pow_right (by norm_num) (by norm_num)⟩
  | succ k hk ih =>
    obtain ⟨h1, h2, h3, h4, hac, hDc, hae, hDe⟩ := ih
    rw [splitQuad3_succ hk, splitPairMax_succ _ _ hk]
    set ac := (splitQuad3 k).1.1
    set Dc := (splitQuad3 k).1.2
    set ae := (splitQuad3 k).2.1
    set De := (splitQuad3 k).2.2
    set a := (splitPairMax splitSeedSmallA splitSeedSmallD k).1
    set D := (splitPairMax splitSeedSmallA splitSeedSmallD k).2
    show 1 ≤ sCountN k ac ∧ 1 ≤ max (fsCountW k ac Dc) (fejerStepThrDeg k Dc) ∧
      1 ≤ sExpN2 k ac ae ∧ 1 ≤ fsExpW2 k ac Dc ae De ∧
      sCountN k ac ≤ splitStepAMax k a ∧
      max (fsCountW k ac Dc) (fejerStepThrDeg k Dc) ≤
        splitStepDMaxWith (fejerStepP k) (fejerStepT k) k a D ∧
      sExpN2 k ac ae ≤ splitStepAMax k a ∧
      fsExpW2 k ac Dc ae De ≤ splitStepDMaxWith (fejerStepP k) (fejerStepT k) k a D
    have hc : sCountN k ac ≤ sCountN k a := by
      simp only [sCountN, sSN, sQrN, sPbN]; gcongr
    have he : sExpN2 k ac ae ≤ sExpN k a := by
      unfold sExpN2 sExpN sLN2 sLN sPbN2 sPbN sSN sQrN sBqN sErN; gcongr
    have hcw : fsCountW k ac Dc ≤ wCountW (fejerStepP k) k a D := by
      simp only [fsCountW, wCountW, fsSW, fsPbW, fsQrW, fsStepY, wSW, wPbW, wStepY]; gcongr
    have hct : fejerStepThrDeg k Dc ≤ wThrDeg (fejerStepP k) D := by
      unfold fejerStepThrDeg wThrDeg; gcongr
    have hew : fsExpW2 k ac Dc ae De ≤ wExpW (fejerStepP k) (fejerStepT k) k a D := by
      unfold fsExpW2 wExpW fsZW wZW fsLW2 wLW fsBqW wBqW fsErW wErW fsEbW wEbW fsPbW2 wPbW fsSW wSW
        fsQrW fsStepY wStepY
      gcongr
    refine ⟨?_, ?_, ?_, ?_, hc.trans (le_max_left _ _), max_le (hcw.trans ?_) (hct.trans (le_max_right _ _)),
      he.trans (le_max_right _ _), hew.trans ((le_max_right _ _).trans (le_max_left _ _))⟩
    · unfold sCountN; omega
    · exact (show 1 ≤ fejerStepThrDeg k Dc by unfold fejerStepThrDeg; omega).trans (le_max_right _ _)
    · unfold sExpN2; omega
    · unfold fsExpW2; omega
    · exact (le_max_left _ _).trans (le_max_left _ _)

/-- **A two-track class in every dimension `k ≥ 2`.** -/
theorem splitUniformClass2_all3 (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k)))) :
    ∀ k, 2 ≤ k →
      Nonempty (SplitUniformClass2 k (classV Kc pc k) (splitQuad3 k).1.1 (splitQuad3 k).1.2
        (splitQuad3 k).2.1 (splitQuad3 k).2.2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hV1 := one_le_classV Kc pc 2
    have hc1 := const_le_classV_succ Kc pc 1
    rw [splitQuad3_two]
    exact splitUniformClass2_two_tight (hK 1) (hp 1) (hlem 1 le_rfl) hV1 (hc1.1.trans le_rfl)
      (hc1.2.trans le_rfl)
  | succ k hk ih =>
    obtain ⟨C⟩ := ih
    obtain ⟨h1, h2, h3, h4, -⟩ := split_quad3_le_max k hk
    have hV1 := one_le_classV Kc pc k
    have hc := const_le_classV_succ Kc pc k
    rw [splitQuad3_succ hk]
    exact splitUniformClass2_succ_fejer (by omega) hV1 h1 h2 h3 h4 C (hK k) (hp k) (hlem k (by omega))
      (classV_le_succ Kc pc k) hc.1 hc.2

/-- The exact two-track class log-degrees in dimensions `0, …, 14`. -/
def tTableT3 : List Nat :=
  [17, 17, 47, 77, 120, 186, 286, 450, 740, 1275, 2298, 4292, 8223, 16027, 31570]

/-- The class log-degree: the exact two-track table up to `14`, constant `5/2` beyond. -/
def tDegT3 (l : Nat) : Nat := if l ≤ 14 then tTableT3.getD l 0 else 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2

/-- The two-track class degree. -/
def uDegT3 (l : Nat) : Nat := 2 ^ tDegT3 l

theorem uDegT3_eq (l : Nat) : uDegT3 l = 2 ^ tDegT3 l := rfl

theorem tDegT3_eq_of_ge {l : Nat} (hl : 15 ≤ l) :
    tDegT3 l = 5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2 + 2 := by
  unfold tDegT3; rw [if_neg (by omega)]

theorem seventeen_le_tDegT3 (l : Nat) : 17 ≤ tDegT3 l := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide
  · rw [tDegT3_eq_of_ge h]
    have : 16 ≤ (l + 4) ^ 2 := by nlinarith
    omega

theorem tDegT3_le_succ (l : Nat) : tDegT3 l ≤ tDegT3 (l + 1) := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide
  · rw [tDegT3_eq_of_ge h, tDegT3_eq_of_ge (by omega)]
    have h1 : 2 ^ (l - 1) ≤ 2 ^ (l + 1 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (l + 4) ^ 2 ≤ (l + 1 + 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega

theorem tDegT3_mono {l k : Nat} (hl : l ≤ k) : tDegT3 l ≤ tDegT3 k := by
  induction k, hl using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact ih.trans (tDegT3_le_succ k)

theorem uDegT3_le_pow {l k : Nat} (hl : l ≤ k) : uDegT3 l ≤ 2 ^ tDegT3 k := by
  rw [uDegT3_eq]; exact Nat.pow_le_pow_right (by norm_num) (tDegT3_mono hl)

/-- **The two-track degrees fit `uDegT3`**, kernel-evaluated up to dimension `14`. -/
theorem split_quad3_le_uDegT3 {l : Nat} (hl : 2 ≤ l) :
    max (splitQuad3 l).1.1 (splitQuad3 l).2.1 + max (splitQuad3 l).1.2 (splitQuad3 l).2.2 + l + 1 ≤
      uDegT3 l := by
  rcases Nat.lt_or_ge l 15 with h | h
  · interval_cases l <;> decide +kernel
  · obtain ⟨-, -, -, -, hac, hDc, hae, hDe⟩ := split_quad3_le_max l hl
    have hM := split_pair_max_le_closed h
    unfold uDegT3; rw [tDegT3_eq_of_ge h]
    have h1 := max_le hac hae
    have h2 := max_le hDc hDe
    omega

/-- **The class cover in dimension `l` at degree `uDegT3 l`.** -/
theorem polyCoverAt_classT3 (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    PolyCoverAt l (uCount (classV Kc pc l) (uDegT3 l)) (uExp (classV Kc pc l) (uDegT3 l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform_low hVl ?_
    unfold uDegT3
    exact Nat.pow_le_pow_right (by norm_num) (seventeen_le_tDegT3 1)
  · obtain ⟨C2⟩ := splitUniformClass2_all3 Kc pc hK hp hlem l hl
    have C := C2.toSplit hVl
    have hfit := split_quad3_le_uDegT3 hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDegT3 l) (by omega) (by omega)
      (by omega)
    refine P0.weaken ?_ ?_ ?_
    · intro g t s hg hg1 ht ht1 hs hs1
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
    · intro g t s _ _ _ _ _ _
      exact (uExp_pos_le _ _ g t s).1
    · intro g t s hg hg1 ht ht1 hs hs1
      show (uCount _ _ g t s)⁻¹ ≤ _
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]

end LeanProofs.GowersSzemeredi
