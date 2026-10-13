import GowersSzemeredi.Proofs18FejerEnvelopeBase
import GowersSzemeredi.Proofs18TightClassesFejer
import GowersSzemeredi.Proofs16UniformCoverTwoSplit
import GowersSzemeredi.Proofs16WeylBudgetGrowth
import GowersSzemeredi.Proofs18CoverSharperLowDegrees
import GowersSzemeredi.Proofs18ShortLengthsFromCubic
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
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le_with
    (fejer_alpha_bounds k ha ha2).1 (fejer_alpha_bounds k ha ha2).2
  obtain ⟨t0, -, ti⟩ := thetaOne_fejer_bounds k ha ha2
  refine ⟨h0, h1, ?_⟩
  exact (section16ThetaTwo_inv_le_pw (two_div_ge_two ha ha2) (by omega) t0 ti)

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
  obtain ⟨ha0, haS⟩ := fejer_alpha_bounds k ha ha2
  obtain ⟨t0, t1, d0, d1⟩ := section16_theta_delta_bounds_with ha0 haS
  have hi := (section16Delta_inv_le_pw (two_div_ge_two ha ha2) (by omega) t0 t1
    (thetaOne_fejer_bounds k ha ha2).2.2)
  exact ⟨d0, d1, pw_mono (two_div_ge_two ha ha2) hi (by omega)⟩

end Fixed

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
theorem split_step_gen {k a D a' D' P T e s : Nat}
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
  have hν : (1 : Real) ≤ (n : Real) + 1 := by have := Nat.cast_nonneg (α := Real) n; linarith
  have h := famTwoCount_le_two_bases hν hW2 hr hrW hM hqf
  unfold uniTwoFejerCount
  exact h.trans (tb_mono hν (by linarith only [hW2]) (by norm_num) (by norm_num))

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

/-- Every component of the two-track recursion is positive. -/
theorem splitQuad3_pos (l : Nat) :
    1 ≤ (splitQuad3 l).1.1 ∧ 1 ≤ (splitQuad3 l).1.2 ∧
      1 ≤ (splitQuad3 l).2.1 ∧ 1 ≤ (splitQuad3 l).2.2 := by
  cases l with
  | zero => norm_num [splitQuad3]
  | succ k =>
    rw [splitQuad3]
    split_ifs with hk
    · norm_num
    · change 1 ≤ sCountN k _ ∧ 1 ≤ max (fsCountW k _ _) (fejerStepThrDeg k _) ∧
        1 ≤ sExpN2 k _ _ ∧ 1 ≤ fsExpW2 k _ _ _ _
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold sCountN; omega
      · exact (show 1 ≤ fejerStepThrDeg k _ by unfold fejerStepThrDeg; omega).trans (le_max_right _ _)
      · unfold sExpN2; omega
      · unfold fsExpW2; omega

/-- A two-track step is bounded by the one-step estimates at common upper bounds. -/
theorem splitQuadStep_le {k ac Dc ae De a D : Nat}
    (hac : ac ≤ a) (hDc : Dc ≤ D) (hae : ae ≤ a) (hDe : De ≤ D) :
    max (sCountN k ac) (sExpN2 k ac ae) ≤ splitStepA k a ∧
      max (max (fsCountW k ac Dc) (fejerStepThrDeg k Dc)) (fsExpW2 k ac Dc ae De) ≤
        splitStepDWith (fejerStepP k) (fejerStepT k) k a D := by
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
  unfold splitStepA splitStepDWith
  omega

/-- The actual two-track degrees satisfy the class invariant at constant `5/2`. -/
theorem split_quad3_half : ∀ l, 12 ≤ l →
    2 ^ (l + 6) * max (splitQuad3 l).1.1 (splitQuad3 l).2.1 ≤ 2 ^ (5 * 2 ^ (l - 1)) ∧
      max (splitQuad3 l).1.2 (splitQuad3 l).2.2 ≤
        2 ^ (5 * 2 ^ (l - 1) + 3 * (l + 4) ^ 2) := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => constructor <;> decide +kernel
  | succ k hk ih =>
    obtain ⟨hAb, hDb⟩ := ih
    set a := max (splitQuad3 k).1.1 (splitQuad3 k).2.1
    set D := max (splitQuad3 k).1.2 (splitQuad3 k).2.2
    have ha : 1 ≤ a := (splitQuad3_pos k).1.trans (le_max_left _ _)
    have hDp : 1 ≤ D := (splitQuad3_pos k).2.1.trans (le_max_left _ _)
    obtain ⟨hAn, hDn⟩ := splitQuadStep_le (k := k) (a := a) (D := D)
      (ac := (splitQuad3 k).1.1) (Dc := (splitQuad3 k).1.2)
      (ae := (splitQuad3 k).2.1) (De := (splitQuad3 k).2.2)
      (le_max_left _ _) (le_max_left _ _) (le_max_right _ _) (le_max_right _ _)
    obtain ⟨h1, h2⟩ := split_step_gen hAb hDb (hAn.trans (splitStepA_le ha))
      (hDn.trans (splitStepDWith_le ha hDp (fejerStepP_ge k))) (fejerStepP_le k) (fejerStepT_le k)
    have he : 2 * (5 * 2 ^ (k - 1)) = 5 * 2 ^ (k + 1 - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]; ring
    rw [splitQuad3_succ (by omega)]
    refine ⟨he ▸ h1, h2.trans (Nat.pow_le_pow_right (by norm_num) ?_)⟩
    have hs : 3 * (k + 1 + 4) ^ 2 = 3 * (k + 4) ^ 2 + 6 * k + 27 := by ring
    rw [← he, hs]
    omega


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
    obtain ⟨h1, h2, h3, h4⟩ := splitQuad3_pos k
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
  · obtain ⟨hA, hD⟩ := split_quad3_half l (by omega)
    set a := max (splitQuad3 l).1.1 (splitQuad3 l).2.1
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
    unfold uDegT3; rw [tDegT3_eq_of_ge h, h4]
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
