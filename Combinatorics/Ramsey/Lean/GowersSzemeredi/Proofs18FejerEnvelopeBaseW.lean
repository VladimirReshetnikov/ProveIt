import GowersSzemeredi.Proofs18FejerEnvelopeBaseQ
import GowersSzemeredi.Proofs18TightClassesFejerT
import GowersSzemeredi.Proofs16WeylBudgetGrowth
import GowersSzemeredi.Proofs18CoverTightBase

/-! **The polynomial base budget** (Notes L.16m).

The base budget `μ₀ = max(μV, fixDegQ k) + 2 ≈ 16·2^k` enters every step of
the Section 18 envelope. Both of its terms are artifacts of comparison
bounds:
* under the Fejér `θ₁` the budget, `θ₂/2` and δ are above `X^(-2^(5k+21))`
  (`…_fejer_bounds5`). They were weakened to `fixDegQ k = 2^(k+4) + 7` only
  because `GenParams.slice_const_le` hard-codes `fixDeg`;
* the explicit family constants satisfy `Kc k + pc k ≤ 2^(2^(4k+16))`
  (`family_constants_poly_le`, from the same estimates as
  `family_constants_tower_le`), not just `2^(2^(2^(k+5)))`. Hence
  `classV ≤ 2^(2^(4k+13))` (`classV_le_poly`).

This module provides `pDeg k = 5k + 21` with the budget bounds at `pDeg`,
`GenParams.slice_const_le_deg` (any budget degree `b ≥ 7`, generated from
`slice_const_le`), `baseCFW_recipPowerLB` (generated from
`baseCFQ_recipPowerLB`), and `sq_le_three_tDeg`, which carries the η side
condition `3(k+4)²` once the base budget no longer does. -/
set_option autoImplicit false
noncomputable section
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

/-- `8VX/B ≤ X^(2^μ₀)`, at any budget degree `b ≥ 7`. -/
theorem slice_const_le_deg {V B : Real} {μV b μ0 : Nat} (ha : 0 < alpha) (ha2 : alpha ≤ 1 / 2)
    (hV : 1 ≤ V) (hVμ : V ≤ 2 ^ (2 ^ μV)) (hB : 0 < B)
    (h7 : 7 ≤ b)
    (hBi : B⁻¹ ≤ (2 / alpha) ^ (2 ^ b)) (hμ0 : max μV b + 2 ≤ μ0) :
    8 * V * (2 / alpha) * B⁻¹ ≤ (2 / alpha) ^ (2 ^ μ0) := by
  have hX := two_div_ge_two ha ha2
  set m := max μV b
  have hm7 : 7 ≤ m := le_trans h7 (le_max_right μV b)
  have hV' : V ≤ (2 / alpha) ^ (2 ^ m) := pw_mono hX (pw_const hX hVμ) (le_max_left _ _)
  have hB' : B⁻¹ ≤ (2 / alpha) ^ (2 ^ m) := pw_mono hX hBi (le_max_right _ _)
  have hm2 : 3 ≤ 2 ^ m :=
    le_trans (by norm_num : 3 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h8 : (8 : Real) ≤ (2 / alpha) ^ (2 ^ m) :=
    pw_const hX (by
      calc (8 : Real) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 ^ m) := pow_le_pow_right₀ (by norm_num) hm2)
  have hXm : 2 / alpha ≤ (2 / alpha) ^ (2 ^ m) := pw_X hX m
  have h1 := pw_mul hX (by norm_num) (by linarith) h8 hV'
  have h2 := pw_mul hX (by positivity) (inv_pos.mpr hB).le hXm hB'
  have h3 := pw_mul hX (by positivity) (by positivity) h1 h2
  have e : 8 * V * (2 / alpha) * B⁻¹ = 8 * V * ((2 / alpha) * B⁻¹) := by ring
  rw [e]
  exact pw_mono hX h3 (by omega)

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
  have hX := two_div_ge_two ha ha2
  obtain ⟨hB0, hB1, hBi⟩ := budget_gen_bounds_fejerW k ha ha2
  have hc := GenParams.slice_const_le_deg (V := V) (B := globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k)
    (μV := μV) (b := pDeg k) (μ0 := μ0) ha ha2 hV hVμ hB0 (seven_le_pDeg k) hBi hμ0
  intro s hs hs1
  have hs2 : 0 < s / 2 := half_pos hs
  have hs21 : s / 2 ≤ 1 := by linarith
  have hg : 0 < alpha / 2 := half_pos ha
  have hg1 : alpha / 2 ≤ 1 := by linarith
  set B := globalBudgetW (fejerThetaOne alpha (alpha / 2) k) k with hBdef
  have hQ1 := one_le_uCount V D (alpha / 2) B (s / 2)
  have hQ0 : 0 < uCount V D (alpha / 2) B (s / 2) := lt_of_lt_of_le zero_lt_one hQ1
  have hQeq := uCount_eq hV D hg hg1 hB0 hB1 hs2 hs21
  rw [GenParams.uniformBase_slice V ha hB0 hs] at hQeq
  show 0 < s / 2 / uCount V D (alpha / 2) B (s / 2) ∧
    s / 2 / uCount V D (alpha / 2) B (s / 2) ≤ 1 ∧
    (s / 2 / uCount V D (alpha / 2) B (s / 2))⁻¹ ≤
      (2 / alpha) ^ (D * 2 ^ μ0 + 1) * s⁻¹ ^ (D + 1)
  refine ⟨div_pos hs2 hQ0, (div_le_one hQ0).mpr (by linarith), ?_⟩
  rw [inv_div, hQeq]
  set X := 2 / alpha with hXdef
  have hsi : 0 ≤ s⁻¹ := (inv_pos.mpr hs).le
  have hcs : 8 * V * X * B⁻¹ * s⁻¹ ≤ X ^ (2 ^ μ0) * s⁻¹ := mul_le_mul_of_nonneg_right hc hsi
  have hpow := pow_le_pow_left₀ (by positivity) hcs D
  have h2X : (2 : Real) ≤ X ^ 1 := by rw [pow_one]; exact hX
  calc (8 * V * X * B⁻¹ * s⁻¹) ^ D / (s / 2) = 2 * (s⁻¹ * (8 * V * X * B⁻¹ * s⁻¹) ^ D) := by
        rw [div_eq_mul_inv, inv_div]; ring
    _ ≤ X ^ 1 * (s⁻¹ * (X ^ (2 ^ μ0) * s⁻¹) ^ D) :=
        mul_le_mul h2X (mul_le_mul_of_nonneg_left hpow hsi) (by positivity) (by positivity)
    _ = X ^ (D * 2 ^ μ0 + 1) * s⁻¹ ^ (D + 1) := by ring

end Fixed

/-- The η side condition `3(k+4)²` fits the class degree. -/
theorem sq_le_three_tDeg (k : Nat) : 3 * (k + 4) ^ 2 ≤ 3 * tDeg k + 5 * k + 37 := by
  rcases Nat.lt_or_ge k 13 with h | h
  · interval_cases k <;> decide
  · rw [tDeg_eq_of_ge h]; omega

/-- **The family-lemma constants are at most `2^(2^(4k+16))`**, given the
shapes the Schmidt layer produces (the estimates of
`family_constants_tower_le`, without the final tower). -/
theorem family_constants_poly_le (k : Nat) {MK : Real} {MP Pu : Nat}
    (hMK : MK ≤ 2 ^ (schmidtKExp k + k + 2)) (hPu : Pu ≤ 1 + (k + 1) * schmidtPBnd k)
    (hMP : MP ≤ (2 * (k + 1 + 1) * Pu + 4) ^ (2 ^ (k + 1))) :
    ((⌈MK⌉₊ : Nat) : Real) + (((k + 1) * MP : Nat) : Real) ≤
      2 ^ ((2 : Nat) ^ (4 * k + 16)) := by
  set E := schmidtKExp k with hEdef
  have hE := schmidtKExp_le k
  have hPB := schmidtPBnd_le k
  have hkA : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have hKc : ⌈MK⌉₊ ≤ 2 ^ (E + k + 2) := by
    have : MK ≤ ((2 ^ (E + k + 2) : Nat) : Real) := by push_cast; exact hMK
    exact (Nat.ceil_le).mpr this
  have hPu' : Pu ≤ 2 ^ (5 * k + 17) := by
    have h1 : (k + 1) * schmidtPBnd k ≤ 2 ^ k * 2 ^ (4 * k + 16) := Nat.mul_le_mul hkA hPB
    have h2 : 2 ^ k * 2 ^ (4 * k + 16) = 2 ^ (5 * k + 16) := by rw [← pow_add]; ring_nf
    have h3 : 2 ^ (5 * k + 17) = 2 ^ (5 * k + 16) * 2 := by rw [pow_succ]
    have h4 : 1 ≤ 2 ^ (5 * k + 16) := Nat.one_le_two_pow
    omega
  have hinner : 2 * (k + 1 + 1) * Pu + 4 ≤ 2 ^ (6 * k + 20) := by
    have h1 : 2 * (k + 1 + 1) ≤ 2 ^ (k + 2) := by
      have h := Nat.lt_two_pow_self (n := k + 1)
      rw [show k + 2 = (k + 1) + 1 by ring, pow_succ]; omega
    have h2 : 2 * (k + 1 + 1) * Pu ≤ 2 ^ (k + 2) * 2 ^ (5 * k + 17) := Nat.mul_le_mul h1 hPu'
    have h3 : 2 ^ (k + 2) * 2 ^ (5 * k + 17) = 2 ^ (6 * k + 19) := by rw [← pow_add]; ring_nf
    have h4 : 2 ^ (6 * k + 20) = 2 ^ (6 * k + 19) * 2 := by rw [pow_succ]
    have h5 : 4 ≤ 2 ^ (6 * k + 19) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (6 * k + 19) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hMP' : (k + 1) * MP ≤ 2 ^ (k + (6 * k + 20) * 2 ^ (k + 1)) := by
    have h1 : MP ≤ 2 ^ ((6 * k + 20) * 2 ^ (k + 1)) :=
      hMP.trans ((Nat.pow_le_pow_left hinner _).trans (le_of_eq (by rw [← pow_mul])))
    calc (k + 1) * MP ≤ 2 ^ k * 2 ^ ((6 * k + 20) * 2 ^ (k + 1)) := Nat.mul_le_mul hkA h1
      _ = 2 ^ (k + (6 * k + 20) * 2 ^ (k + 1)) := by rw [← pow_add]
  have hP14 : k + 2 ≤ 2 ^ (4 * k + 14) := by
    have h1 : k + 2 < 2 ^ (k + 2) := Nat.lt_two_pow_self
    have h2 : 2 ^ (k + 2) ≤ 2 ^ (4 * k + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hexp1 : E + k + 2 ≤ 2 ^ (4 * k + 14) + 2 ^ (4 * k + 14) := by omega
  have hexp2 : k + (6 * k + 20) * 2 ^ (k + 1) ≤ 2 ^ (4 * k + 14) + 2 ^ (4 * k + 14) := by
    have h1 : 6 * k + 20 ≤ 2 ^ (k + 5) := by
      have : k < 2 ^ k := Nat.lt_two_pow_self
      have h32 : 2 ^ (k + 5) = 2 ^ k * 32 := by rw [pow_add]; norm_num
      omega
    have h2 : (6 * k + 20) * 2 ^ (k + 1) ≤ 2 ^ (k + 5) * 2 ^ (k + 1) := Nat.mul_le_mul_right _ h1
    have h3 : 2 ^ (k + 5) * 2 ^ (k + 1) = 2 ^ (2 * k + 6) := by rw [← pow_add]; ring_nf
    have h4 : 2 ^ (2 * k + 6) ≤ 2 ^ (4 * k + 14) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : k ≤ 2 ^ (4 * k + 14) := by omega
    calc k + (6 * k + 20) * 2 ^ (k + 1) ≤ 2 ^ (4 * k + 14) + 2 ^ (2 * k + 6) := by
          rw [← h3]; exact Nat.add_le_add h5 h2
      _ ≤ 2 ^ (4 * k + 14) + 2 ^ (4 * k + 14) := Nat.add_le_add_left h4 _
  have hsum : ⌈MK⌉₊ + (k + 1) * MP ≤ 2 ^ (2 ^ (4 * k + 14) + 2 ^ (4 * k + 14) + 1) := by
    have hA := hKc.trans (Nat.pow_le_pow_right (by norm_num) hexp1)
    have hB := hMP'.trans (Nat.pow_le_pow_right (by norm_num) hexp2)
    rw [pow_succ]
    omega
  have hfin : 2 ^ (2 ^ (4 * k + 14) + 2 ^ (4 * k + 14) + 1) ≤ 2 ^ (2 ^ (4 * k + 16)) := by
    apply Nat.pow_le_pow_right (by norm_num)
    have h1 : 2 ^ (4 * k + 16) = 4 * 2 ^ (4 * k + 14) := by
      rw [show 4 * k + 16 = (4 * k + 14) + 2 by ring, pow_add]; ring
    have h2 : 1 ≤ 2 ^ (4 * k + 14) := Nat.one_le_two_pow
    omega
  have hcast : ((⌈MK⌉₊ + (k + 1) * MP : Nat) : Real) ≤ ((2 ^ (2 ^ (4 * k + 16)) : Nat) : Real) := by
    exact_mod_cast hsum.trans hfin
  push_cast at hcast ⊢
  exact hcast

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
