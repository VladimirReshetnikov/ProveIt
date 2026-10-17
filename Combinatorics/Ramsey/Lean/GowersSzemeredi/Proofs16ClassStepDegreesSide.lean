import GowersSzemeredi.Proofs16ClassStepDegrees
import GowersSzemeredi.Proofs16ClassStepBounds
import GowersSzemeredi.Proofs16ClassStepSide

/-! Declarations of `Proofs16ClassStepDegrees` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

theorem twoDiv_budget_le {gamma theta g : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg0 : 0 < g)
    (hgi : 2 / g ≤ (2 / (gamma * theta)) ^ (2 ^ (2 ^ (k + 5) + 5) + 1)) :
    2 / (g * classBudget theta gamma k) ≤ (2 / (gamma * theta)) ^ (stepP k + 1) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, -⟩ := classBudget_pos_le k ht ht1 hg hg1
  have hbi := classBudget_inv_le k hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  rw [show 2 / (g * classBudget theta gamma k) = 2 / g * (classBudget theta gamma k)⁻¹ by
    field_simp]
  calc 2 / g * (classBudget theta gamma k)⁻¹
      ≤ u ^ (2 ^ (2 ^ (k + 5) + 5) + 1) * u ^ (2 ^ (2 ^ (k + 5) + 5)) :=
        mul_le_mul hgi hbi (inv_pos.mpr hb).le (pow_nonneg hupos.le _)
    _ = u ^ (2 ^ (2 ^ (k + 5) + 5) + 1 + 2 ^ (2 ^ (k + 5) + 5)) := by rw [← pow_add]
    _ = u ^ (stepP k + 1) := by
        congr 1
        unfold stepP
        rw [show 2 ^ (k + 5) + 6 = (2 ^ (k + 5) + 5) + 1 by omega, pow_succ]
        ring

theorem twoDiv_delta_le {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    2 / (classDelta theta gamma k * classBudget theta gamma k) ≤
      (2 / (gamma * theta)) ^ (stepP k + 1) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨-, -, hd, -⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  have hdi := classDelta_inv_le k hg hg1 ht ht1
  refine twoDiv_budget_le k hg hg1 ht ht1 hd ?_
  rw [div_eq_mul_inv, pow_succ, mul_comm]
  exact mul_le_mul hdi hu2 (by norm_num) (pow_nonneg (by linarith) _)

theorem twoDiv_gamma_le {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    2 / (gamma * classBudget theta gamma k) ≤ (2 / (gamma * theta)) ^ (stepP k + 1) := by
  obtain ⟨hu2, -, h2g, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  refine twoDiv_budget_le k hg hg1 ht ht1 hg ?_
  have hu1 : 1 ≤ 2 / (gamma * theta) := le_trans (by norm_num) hu2
  refine h2g.trans ?_
  calc 2 / (gamma * theta) = (2 / (gamma * theta)) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ hu1 (Nat.le_add_left 1 _)

theorem stepP_ge (k : Nat) : k + 8 ≤ stepP k := by
  unfold stepP
  have h1 := two_pow_k5_ge k
  have h2 : 2 ^ (k + 5) + 6 < 2 ^ (2 ^ (k + 5) + 6) := Nat.lt_two_pow_self
  omega

theorem classPieces_le_stepP {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (classPieces gamma theta k : Real) ≤ (2 / (gamma * theta)) ^ stepP k :=
  classPieces_le_gen k hg hg1 ht ht1

/-- **The count of the next class.** -/
theorem step_count_le {k D : Nat} (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    max (famPieceGraphBound (classQr V D k (n * classPieces gamma theta k) (classBudget theta gamma k) gamma)
        (classPb V D (n * classPieces gamma theta k) (classBudget theta gamma k) gamma)
        (n * classPieces gamma theta k) rho)
      (((3 ^ (k + 1) * (n * classPieces gamma theta k)) : Nat) : Real) ≤
      uniformBase V' n theta gamma rho ^ stepCountDeg k D :=
  step_count_le_W hD hV hVV hg hg1 ht ht1 hr hr1 n (P := stepP k)
    (classBudget_pos_le k ht ht1 hg hg1).1 (classPieces_le_stepP k hg hg1 ht ht1)
    (twoDiv_gamma_le k hg hg1 ht ht1) (stepP_ge k)

/-- **The width exponent of the next class.** -/
theorem step_exp_inv_le {k D : Nat} (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPieces gamma theta k
    let tS := classBudget theta gamma k
    let gS := classDelta theta gamma k
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (classQb V D M tS gS) (classEb V D M tS gS)
            (classEr V D k M tS gamma) rho *
          famPieceSliceExponent (classQr V D k M tS gamma) (classEs V D M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (classQb V D M tS gS) (section16Zeta theta gamma k) rho)
          (pieceLineExponent (familyWidthDivisor k p) (classQb V D M tS gS) (classEb V D M tS gS)
            (classEr V D k M tS gamma) rho)
          (famPieceSliceExponent (classQr V D k M tS gamma) (classEs V D M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ uniformBase V' n theta gamma rho ^ stepExpDeg k D :=
  have hb := classBudget_pos_le k ht ht1 hg hg1
  have hd := section16_theta_delta_bounds k ht ht1 hg hg1
  step_exp_inv_le_W hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n (P := stepP k) (T := stepT k)
    hb.1 hb.2 hd.2.2.1 hd.2.2.2 (section16Zeta_inv_le_gen k hg ht)
    (classPieces_le_stepP k hg hg1 ht ht1) (twoDiv_gamma_le k hg hg1 ht ht1)
    (twoDiv_delta_le k hg hg1 ht ht1) (stepP_ge k)

theorem step_thr_le {k D : Nat} (hk : 1 ≤ k) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    classStepThreshold V D theta gamma k ≤ (V' * (2 / (gamma * theta))) ^ stepThrDeg k D := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hL := lemma156ExplicitThreshold_le_gen hk hg hg1 ht ht1
  have hgd := twoDiv_gamma_le k hg hg1 ht ht1
  have hdd := twoDiv_delta_le k hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hV' : 1 ≤ V' := hV.trans hVV
  have hu1 : 1 ≤ u := le_trans (by norm_num) hu2
  have hua : u ≤ V' * u := le_mul_of_one_le_left (by linarith) hV'
  have ha2 : 2 ≤ V' * u := hu2.trans hua
  have ha1 : 1 ≤ V' * u := le_trans (by norm_num) ha2
  have hpow : ∀ j : Nat, V * u ^ j ≤ (V' * u) ^ (j + 1) := by
    intro j
    rw [pow_succ']
    exact mul_le_mul (hVV.trans (le_mul_of_one_le_right (by linarith) hu1))
      (pow_le_pow_left₀ (by linarith) hua j) (pow_nonneg (by linarith) _) (by linarith)
  have hpiece : ∀ g : Real, 0 < g → 2 / (g * classBudget theta gamma k) ≤ u ^ (stepP k + 1) →
      (V * (2 / (g * classBudget theta gamma k))) ^ D ≤ (V' * u) ^ stepThrDeg k D := by
    intro g hg0 hgi
    have h1 : V * (2 / (g * classBudget theta gamma k)) ≤ (V' * u) ^ (stepP k + 1 + 1) :=
      (mul_le_mul_of_nonneg_left hgi (by linarith)).trans (hpow _)
    have h0 : 0 ≤ V * (2 / (g * classBudget theta gamma k)) := by
      obtain ⟨hb, -⟩ := classBudget_pos_le k ht ht1 hg hg1
      have : 0 < g * classBudget theta gamma k := mul_pos hg0 hb
      exact mul_nonneg (by linarith) (div_nonneg (by norm_num) this.le)
    have h2 := pow_le_pow_left₀ h0 h1 D
    rw [← pow_mul] at h2
    refine h2.trans (pow_le_pow_right₀ ha1 ?_)
    unfold stepThrDeg
    have : (stepP k + 1 + 1) * D = D * (stepP k + 2) := by ring
    omega
  unfold classStepThreshold classPieceThreshold
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · have h3 : (3 : Real) ≤ (V' * u) ^ 2 := by nlinarith only [ha2]
    exact h3.trans (pow_le_pow_right₀ ha1 (by unfold stepThrDeg; omega))
  · refine hL.trans ((pow_le_pow_left₀ (by linarith) hua _).trans (pow_le_pow_right₀ ha1 ?_))
    unfold stepThrDeg
    rw [← stepP]
    omega
  · obtain ⟨-, -, hd, -⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
    exact hpiece _ hd hdd
  · exact hpiece _ hg hgd

/-- **The step of route (II).** A uniform class of dimension `k ≥ 1` at one
degree `D`, with the family Lemma 16.6 at dimension `k`, gives a uniform class
of dimension `k+1`. -/
theorem powerUniformClass_succ {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V) {D : Nat}
    (hD : 1 ≤ D) (C : PowerUniformClass k V D D D) {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    Nonempty (PowerUniformClass (k + 1) V' (stepCountDeg k D) (stepExpDeg k D) (stepThrDeg k D)) := by
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (classPieces gamma theta k) → StepPiece C N theta gamma,
        Gamma ⊆ stepPieceGraphs C P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => ClassPiece.empty C _ _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    have hN' : classStepThreshold V D theta gamma k ≤ N :=
      (step_thr_le hk hV hVV hg hg1 ht ht1).trans hN
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover C hk hV (familyWidthPrefactor_pos hK) (familyWidthDivisor_pos hp)
      hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      exact step_count_le hD hV hVV hg hg1 ht ht1 hr hr1 n
    · intro rho hr hr1
      have h2 := uniformBase_two_le (hV.trans hVV) n ht ht1 hg hg1 hr hr1
      positivity
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := step_exp_inv_le hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      have := inv_anti₀ (inv_pos.mpr he0) hei
      rwa [inv_inv] at this

end

end LeanProofs.GowersSzemeredi
