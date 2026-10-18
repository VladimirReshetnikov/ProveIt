import GowersSzemeredi.Proofs18GenericEnvelopeBase
import GowersSzemeredi.Proofs18LengthSixCountsSide

/-! Declarations of `Proofs18GenericEnvelopeBase` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
variable {alpha : Real}

/-- The log-degree of the fixed parameters of dimension `k`. -/
def fixDeg (k : Nat) : Nat := 2 ^ (k + 5) + 7

/-- **The Bohr radius**: `ζ⁻¹ = 2^(multipleS) ≤ exp(X^(2^(2^(k+6)+1)))`. -/
theorem zeta_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Zeta alpha (alpha / 2) k ∧
      (section16Zeta alpha (alpha / 2) k)⁻¹ ≤ Real.exp ((2 / alpha) ^ (2 ^ (2 ^ (k + 6) + 1))) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨hz, -⟩ := section16Zeta_pos_le_half k ha ha1 (half_pos ha) (by linarith)
  have hX := two_div_ge_two ha ha2
  refine ⟨hz, ?_⟩
  have hS : multipleS alpha (alpha / 2) k = ((2 / alpha) ^ 2) ^ (2 ^ 2 ^ (k + 6)) := by
    unfold multipleS
    congr 1
    field_simp
  have hS0 : 0 ≤ multipleS alpha (alpha / 2) k := by rw [hS]; positivity
  unfold section16Zeta
  rw [Real.rpow_neg (by norm_num), inv_inv]
  refine (two_rpow_le_exp hS0).trans (Real.exp_le_exp.mpr ?_)
  rw [hS, ← pow_mul]
  exact pow_le_pow_right₀ (le_trans (by norm_num) hX) (le_of_eq (by ring))

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi.GenParams

section
variable {alpha : Real}

/-- `8VX/B ≤ X^(2^μ₀)`. -/
theorem slice_const_le {V B : Real} {μV k μ0 : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV)) (hB : 0 < B)
    (hBi : B⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k)) (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) :
    8 * V * (2 / alpha) * B⁻¹ ≤ (2 / alpha) ^ (2 ^ μ0) := by
  exact slice_const_le_deg ha ha2 hV hVμ hB
    (show 7 ≤ fixDeg k from Nat.le_add_left 7 _) hBi hμ0

theorem sq_add_three_lt (k : Nat) : (k + 3) * (k + 3) < 2 ^ (k + 5) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show k + 1 + 5 = (k + 5) + 1 by ring, pow_succ]
    nlinarith

theorem fixDeg_cube (k : Nat) : 2 * (k + 2) ^ 3 + k + 3 ≤ 2 ^ fixDeg k ∧
    2 * (2 * (k + 3)) ^ (k + 3) ≤ 2 ^ fixDeg k := by
  have hk2 : k + 2 < 2 ^ (k + 2) := Nat.lt_two_pow_self
  have hk3 : 2 * (k + 3) ≤ 2 ^ (k + 3) := by
    have := Nat.lt_two_pow_self (n := k + 2); rw [pow_succ]; omega
  have hexp : 3 * k + 9 ≤ 2 ^ (k + 5) := by
    have : 2 ^ (k + 5) = 8 * 2 ^ (k + 2) := by rw [show k + 5 = (k + 2) + 3 by ring, pow_add]; ring
    omega
  have hsq := sq_add_three_lt k
  unfold fixDeg
  constructor
  · have h3 : (k + 2) ^ 3 ≤ (2 ^ (k + 2)) ^ 3 := Nat.pow_le_pow_left hk2.le 3
    have h4 : (2 ^ (k + 2)) ^ 3 = 2 ^ (3 * k + 6) := by rw [← pow_mul]; ring_nf
    have h5 : 2 ^ (3 * k + 6) * 4 ≤ 2 ^ (2 ^ (k + 5) + 7) := by
      rw [show 2 ^ (3 * k + 6) * 4 = 2 ^ (3 * k + 8) by rw [pow_add]; ring]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h6 : k + 3 ≤ 2 ^ (3 * k + 6) := by
      have := Nat.lt_two_pow_self (n := 3 * k + 6); omega
    omega
  · have h3 : (2 * (k + 3)) ^ (k + 3) ≤ (2 ^ (k + 3)) ^ (k + 3) := Nat.pow_le_pow_left hk3 _
    have h4 : (2 ^ (k + 3)) ^ (k + 3) = 2 ^ ((k + 3) * (k + 3)) := by rw [← pow_mul]
    have h5 : 2 * 2 ^ ((k + 3) * (k + 3)) ≤ 2 ^ (2 ^ (k + 5) + 7) := by
      rw [show 2 * 2 ^ ((k + 3) * (k + 3)) = 2 ^ ((k + 3) * (k + 3) + 1) by ring]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end

end LeanProofs.GowersSzemeredi.GenParams

namespace LeanProofs.GowersSzemeredi.GenParams

section
variable {alpha : Real}
variable {X : Real}

/-- The single-piece density `θ·c(c(θ))` for a reciprocal-power `c`. -/
theorem dens_step (hX : 2 ≤ X) {c : Real → Real} {a0 b0 : Nat} (hc : RecipPowerLB X c a0 b0)
    {θ : Real} {m μa μb : Nat} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hθi : θ⁻¹ ≤ X ^ (2 ^ m))
    (ha0 : a0 ≤ 2 ^ μa) (hb0 : b0 ≤ 2 ^ μb) (hμa : μa ≤ m) :
    0 < θ * c (c θ) ∧ θ * c (c θ) ≤ 1 ∧ (θ * c (c θ))⁻¹ ≤ X ^ (2 ^ (m + 2 * μb + 4)) := by
  obtain ⟨hc0, hc1, hci⟩ := cS_step hX hc hθ0 hθ1 hθi ha0 hb0 hμa
  obtain ⟨hd0, hd1, hdi⟩ := cS_step hX hc hc0 hc1 hci ha0 hb0 (by omega)
  refine ⟨mul_pos hθ0 hd0, (mul_le_mul hθ1 hd1 hd0.le zero_le_one).trans (by norm_num), ?_⟩
  rw [mul_inv]
  have := pw_mul' hX (inv_pos.mpr hd0).le hθi hdi
  exact pw_mono hX this (by omega)

end

end LeanProofs.GowersSzemeredi.GenParams

namespace LeanProofs.GowersSzemeredi.GenParams

section
variable {alpha : Real}

/-- `η` from the single-piece density. -/
theorem eta_step {alpha d : Real} {k m : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hd0 : 0 < d) (hd1 : d ≤ 1) (hdi : d⁻¹ ≤ (2 / alpha) ^ (2 ^ m)) (hm : fixDeg k ≤ m) :
    0 < (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ∧
      (2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4) ≤
        alpha / 8 ∧
      ((2 : Real) ^ (-(2 * ((k + 1) + 1) ^ 3 : Int)) * (d / (2 : Real) ^ (k + 1) * alpha ^ 2 / 4))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (m + 1)) := by
  exact eta_step_of_cube_le ha ha2 hd0 hd1 hdi
    ((fixDeg_cube k).1.trans (Nat.pow_le_pow_right (by norm_num) hm))

/-- `yIn` from `η`. -/
theorem yIn_step {alpha e : Real} {k m : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (he0 : 0 < e) (he8 : e ≤ alpha / 8) (hei : e⁻¹ ≤ (2 / alpha) ^ (2 ^ m)) (hm : fixDeg k ≤ m) :
    0 < (e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ∧
      (e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2) ≤ alpha ∧
      ((e / 2) / (2 * (k + 1 + 2 : Nat) : Real) ^ (k + 1 + 2))⁻¹ ≤ (2 / alpha) ^ (2 ^ (m + 1)) := by
  exact yIn_step_of_den_le ha ha2 he0 he8 hei
    ((fixDeg_cube k).2.trans (Nat.pow_le_pow_right (by norm_num)
      (hm.trans (Nat.le_of_lt (Nat.lt_two_pow_self (n := m))))))

end

end LeanProofs.GowersSzemeredi.GenParams

namespace LeanProofs.GowersSzemeredi

theorem uCount_scale_le {X V γ θ s : Real} {D μV μD μ0 c : Nat} (hX : 2 ≤ X) (hV : 1 ≤ V)
    (hVμ : V ≤ 2 ^ (2 ^ μV)) {k : Nat} (hμ0 : max μV (fixDeg k) + 2 ≤ μ0)
    (hg : 0 < γ) (hg1 : γ ≤ 1) (hgi : γ⁻¹ ≤ X ^ (2 ^ fixDeg k))
    (ht : 0 < θ) (ht1 : θ ≤ 1) (hti : θ⁻¹ ≤ X ^ (2 ^ fixDeg k))
    (hs : 0 < s) (hs1 : s ≤ 1) (hsi : s⁻¹ ≤ X ^ (2 ^ c)) (hD : D ≤ 2 ^ μD) :
    uCount V D γ θ s ≤ X ^ (2 ^ (max μ0 c + 1 + μD)) := by
  rw [uCount_eq hV D hg hg1 ht ht1 hs hs1]
  have hval : uniformBase V 1 θ γ s = 4 * V * γ⁻¹ * θ⁻¹ * s⁻¹ := by
    unfold uniformBase; field_simp; ring
  rw [hval]
  set m := max μV (fixDeg k)
  have h7 : 7 ≤ m := le_trans (Nat.le_add_left 7 _) (le_max_right μV (fixDeg k))
  have h4 : (4 : Real) ≤ X ^ (2 ^ m) :=
    pw_mono hX (pw_const hX (a := 1) (by norm_num)) (by omega)
  have hV' : V ≤ X ^ (2 ^ m) := pw_mono hX (pw_const hX hVμ) (le_max_left _ _)
  have hg' : γ⁻¹ ≤ X ^ (2 ^ m) := pw_mono hX hgi (le_max_right _ _)
  have ht' : θ⁻¹ ≤ X ^ (2 ^ m) := pw_mono hX hti (le_max_right _ _)
  have h1 := pw_mul hX (by linarith) h4 hV'
  have h2 := pw_mul hX (inv_pos.mpr ht).le hg' ht'
  have h3 := pw_mul hX (by positivity) h1 h2
  have hc0 : 4 * V * γ⁻¹ * θ⁻¹ ≤ X ^ (2 ^ μ0) := by
    rw [show 4 * V * γ⁻¹ * θ⁻¹ = 4 * V * (γ⁻¹ * θ⁻¹) by ring]
    exact pw_mono hX h3 (by omega)
  have h5 := pw_mul' hX (inv_pos.mpr hs).le hc0 hsi
  exact pw_pow hX (by positivity) h5 hD

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi.GenParams

section
variable {alpha : Real}

/-- `(α/2)⁻¹ = X`. -/
theorem half_inv_le (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    (alpha / 2)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  rw [inv_div]; exact pw_X (two_div_ge_two ha ha2) _

end

end LeanProofs.GowersSzemeredi.GenParams

namespace LeanProofs.GowersSzemeredi

theorem selection_degree_le (k : Nat) :
    (7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) + 46) * arrangementSelectionExponent k ≤
      2 ^ (2 ^ (k + 4) + 4 * k + 11) := by
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h21 : 7 + 21 * k ≤ 2 ^ (k + 5) := by
    have : 2 ^ (k + 5) = 32 * 2 ^ k := by rw [pow_add]; ring
    omega
  have h4 : 4 ^ (k + 1) = 2 ^ (2 * k + 2) := by
    rw [show (4 : Nat) = 2 ^ 2 by norm_num, ← pow_mul]; ring_nf
  have hprod : (7 + 21 * k) * 4 ^ (k + 1) ≤ 2 ^ (3 * k + 7) := by
    rw [h4]
    calc (7 + 21 * k) * 2 ^ (2 * k + 2) ≤ 2 ^ (k + 5) * 2 ^ (2 * k + 2) := Nat.mul_le_mul_right _ h21
      _ = 2 ^ (3 * k + 7) := by rw [← pow_add]; ring_nf
  have h46 : 46 ≤ 2 ^ (3 * k + 7) := le_trans (by norm_num : 46 ≤ 2 ^ 7)
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hsum : 7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) + 46 ≤ 2 ^ (3 * k + 8) := by
    have e : 7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) = (7 + 21 * k) * 4 ^ (k + 1) := by ring
    have : 2 ^ (3 * k + 8) = 2 * 2 ^ (3 * k + 7) := by rw [pow_succ]; ring
    omega
  unfold arrangementSelectionExponent
  calc (7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1) + 46) * 2 ^ (2 ^ (k + 4) + k + 3)
      ≤ 2 ^ (3 * k + 8) * 2 ^ (2 ^ (k + 4) + k + 3) := Nat.mul_le_mul_right _ hsum
    _ = 2 ^ (2 ^ (k + 4) + 4 * k + 11) := by rw [← pow_add]; ring_nf

/-- The log-log-degree of the recurrence constants in dimension `k`. -/
def genMuK (k : Nat) : Nat := 2 ^ (k + 5)

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

section
variable {alpha : Real}

theorem thetaOne_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16ThetaOne alpha (alpha / 2) k ∧ section16ThetaOne alpha (alpha / 2) k ≤ 1 ∧
      (section16ThetaOne alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2)) := by
  have ha1 : alpha ≤ 1 := by linarith
  obtain ⟨h0, h1, -, -⟩ := section16_theta_delta_bounds k ha ha1 (half_pos ha) (by linarith)
  have hX := two_div_ge_two ha ha2
  have hq0 : 0 < alpha * (alpha / 2) / 4 := by positivity
  refine ⟨h0, h1, ?_⟩
  unfold section16ThetaOne
  rw [← inv_pow]
  have hq := quarter_base_inv_le ha ha2
  calc (alpha * (alpha / 2) / 4)⁻¹ ^ (2 ^ 2 ^ (k + 5)) ≤ ((2 / alpha) ^ 3) ^ (2 ^ 2 ^ (k + 5)) :=
        pow_le_pow_left₀ (inv_pos.mpr hq0).le hq _
    _ = (2 / alpha) ^ (3 * 2 ^ 2 ^ (k + 5)) := by rw [← pow_mul]
    _ ≤ (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 2)) := by
        apply pow_le_pow_right₀ (le_trans (by norm_num) hX)
        have h : 2 ^ (2 ^ (k + 5) + 2) = 2 ^ (2 ^ (k + 5)) * 4 := by rw [pow_add]; norm_num
        omega

theorem thetaTwo_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16ThetaTwo (section16ThetaOne alpha (alpha / 2) k) ∧
      section16ThetaTwo (section16ThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16ThetaTwo (section16ThetaOne alpha (alpha / 2) k))⁻¹ ≤
        (2 / alpha) ^ (2 ^ (2 ^ (k + 5) + 6)) := by
  obtain ⟨h0, h1⟩ := section16ThetaTwo_pos_le (gamma := alpha / 2) k ha
    (by linarith) (half_pos ha) (by linarith)
  obtain ⟨t0, -, ti⟩ := thetaOne_gen_bounds k ha ha2
  refine ⟨h0, h1, ?_⟩
  exact (section16ThetaTwo_inv_le_pw (two_div_ge_two ha ha2)
    (by have := Nat.lt_two_pow_self (n := k + 5); omega) t0 ti)

theorem budget_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalBudget alpha (alpha / 2) k ∧ globalBudget alpha (alpha / 2) k ≤ 1 ∧
      (globalBudget alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  have hk : k + 2 ≤ 2 ^ (k + 5) + 6 := by
    have := Nat.lt_two_pow_self (n := k + 5); omega
  exact density_div_bounds_pw (two_div_ge_two ha ha2) (thetaTwo_gen_bounds k ha ha2)
    (by have : (1 : Real) ≤ 2 ^ k := one_le_pow₀ (by norm_num); linarith)
    (budget_denominator_le_pw (two_div_ge_two ha ha2) hk)

theorem T2_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < globalTheta2 alpha (alpha / 2) k ∧ globalTheta2 alpha (alpha / 2) k ≤ 1 ∧
      (globalTheta2 alpha (alpha / 2) k)⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  exact density_div_bounds_pw (two_div_ge_two ha ha2) (thetaTwo_gen_bounds k ha ha2)
    (by norm_num) ((two_div_ge_two ha ha2).trans (pw_X (two_div_ge_two ha ha2) _))

theorem delta_gen_bounds (k : Nat) (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2) :
    0 < section16Delta (section16ThetaOne alpha (alpha / 2) k) ∧
      section16Delta (section16ThetaOne alpha (alpha / 2) k) ≤ 1 ∧
      (section16Delta (section16ThetaOne alpha (alpha / 2) k))⁻¹ ≤ (2 / alpha) ^ (2 ^ fixDeg k) := by
  obtain ⟨t0, t1, d0, d1⟩ := section16_theta_delta_bounds k ha (by linarith)
    (half_pos ha) (by linarith)
  have hi := (section16Delta_inv_le_pw (two_div_ge_two ha ha2)
    (by have := Nat.lt_two_pow_self (n := k + 5); omega) t0 t1
    (thetaOne_gen_bounds k ha ha2).2.2)
  exact ⟨d0, d1, pw_mono (two_div_ge_two ha ha2) hi (by unfold fixDeg; omega)⟩

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

/-- The uniform slice density is a reciprocal power, independently of any
single-piece parameter structure. -/
theorem uniform_baseC_recipPowerLB {alpha V : Real} {D k μV μ0 : Nat} (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV))
    (hμ0 : max μV (fixDeg k) + 2 ≤ μ0) :
    RecipPowerLB (2 / alpha)
      (fun s => s / 2 / uCount V D (alpha / 2) (globalBudget alpha (alpha / 2) k) (s / 2))
      (D * 2 ^ μ0 + 1) (D + 1) := by
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds k ha ha2
  exact uniform_baseC_recipPowerLB_of_budget ha ha2 hV hVμ hB0 hB1
    (show 7 ≤ fixDeg k from Nat.le_add_left 7 _) hBi hμ0

/-- **Lemma 15.6's threshold in dimension `k ≥ 1`.** -/
theorem lemma156_gen_le {alpha : Real} {k : Nat} (hk : 1 ≤ k) (ha : 0 < alpha)
    (ha2 : alpha ≤ 1 / 2) :
    lemma156ExplicitThreshold k (alpha / 2) (alpha / 2) ≤
      (2 / alpha) ^ (2 ^ (2 ^ (k + 4) + 4 * k + 13)) := by
  have hX := two_div_ge_two ha ha2
  have hXa : (alpha / 2)⁻¹ = 2 / alpha := inv_div _ _
  set u := 2 / alpha
  have hinv : u⁻¹ = alpha / 2 := by rw [← hXa, inv_inv]
  set N1 := 7 * 4 ^ (k + 1) + 21 * k * 4 ^ (k + 1)
  set E := arrangementSelectionExponent k
  have hdeg := selection_degree_le k
  -- the selection base `a = (α/2)^N1 = u^(-N1)`
  have hbase : (u ^ N1)⁻¹ = (alpha / 2) ^ (7 * 4 ^ (k + 1)) * (alpha / 2) ^ (21 * k * 4 ^ (k + 1)) := by
    rw [← pow_add, ← hinv, inv_pow]
  have hexp : 2 ^ (k + 5) + k + ((N1 + 46) * E + 2) ≤ 2 ^ (2 ^ (k + 4) + 4 * k + 13) := by
    have h1 : 2 ^ (k + 5) + k + 2 ≤ 2 ^ (2 ^ (k + 4) + 4 * k + 11) := by
      have h := Nat.lt_two_pow_self (n := k + 5)
      have : 2 * 2 ^ (k + 5) ≤ 2 ^ (2 ^ (k + 4) + 4 * k + 11) := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by
          have := Nat.lt_two_pow_self (n := k + 4); omega)
      omega
    have h2 : 2 ^ (2 ^ (k + 4) + 4 * k + 13) = 4 * 2 ^ (2 ^ (k + 4) + 4 * k + 11) := by
      rw [show 2 ^ (k + 4) + 4 * k + 13 = (2 ^ (k + 4) + 4 * k + 11) + 2 by ring, pow_add]; ring
    generalize (N1 + 46) * E = P at hdeg ⊢
    omega
  exact lemma156ExplicitThreshold_le_power_of_selection_base hk hX hbase.le (by
    simpa only [show 32 * 2 ^ k = 2 ^ (k + 5) by rw [pow_add]; ring] using hexp)

end LeanProofs.GowersSzemeredi
