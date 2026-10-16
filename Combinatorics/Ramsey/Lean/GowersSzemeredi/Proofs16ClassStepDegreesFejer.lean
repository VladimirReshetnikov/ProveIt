import GowersSzemeredi.Proofs16ClassStepDegrees
import GowersSzemeredi.Proofs16ClassStepBoundsFejer

/-! **The class-step degrees under the Fejér θ₁ and the tight radius**
(Notes L.16d).

The Fejér instance of `Proofs16ClassStepDegrees`: its degrees are the
`…W` degrees at `(fejerStepP k, fejerStepT k)`, and the count and the width
exponent are `step_count_le_W` and `step_exp_inv_le_W` there. Given a uniform class
of dimension `k ≥ 1` at one degree `D`, and the family Lemma 16.6 at
dimension `k` with constants `K, p ≤ V′`, the relations covered by Fejér step
pieces (`StepPieceFejer`) form a uniform class of dimension `k+1` at base
`V′`, with degrees
* `fejerStepCountDeg k D`, `fejerStepExpDeg k D`, `fejerStepThrDeg k D`.

These are the corpus's degrees with `P = fejerStepP k = 64·F` in place of
`stepP k = 2^(2^(k+5)+6)` and `T = fejerStepT k = 22·F + 105` in place of
`stepT k = 2^(2^(k+6))`, where `F = fejerProductExponent k ≤ 2^(5k+14)`.
So every degree is `D · 2^(O(k))` rather than `D · 2^(2^(O(k)))`.

The six inputs are `Proofs16ClassStepBoundsFejer`. The generic lemmas
(`level_base_le`, `step_w_facts`, `inv_scale_le`, `classVertexNum_succ_le`,
`PowerUniformClass.weaken`) are reused from `Proofs16ClassStepDegrees`.

* `powerUniformClass_succ_fejer`: **the Fejér step of route (II)**. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The degrees -/

/-- The count degree of the next class. -/
def fejerStepCountDeg (k D : Nat) : Nat := stepCountDegW (fejerStepP k) k D

/-- The width-exponent degree of the next class. -/
def fejerStepExpDeg (k D : Nat) : Nat := stepExpDegW (fejerStepP k) (fejerStepT k) k D

/-- The threshold degree of the next class. -/
def fejerStepThrDeg (k D : Nat) : Nat := D * (fejerStepP k + 2) + fejerStepP k + 2

/-! ### Bases -/

theorem twoDiv_budget_le_fejer {gamma theta g : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg0 : 0 < g)
    (hgi : 2 / g ≤ (2 / (gamma * theta)) ^ (32 * fejerProductExponent k + 1)) :
    2 / (g * classBudgetW (fejerThetaOne theta gamma k) k) ≤ (2 / (gamma * theta)) ^ (fejerStepP k + 1) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨hb, -⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  have hbi := classBudgetW_fejer_inv_le k hg hg1 ht ht1
  set u := 2 / (gamma * theta) with hu
  clear_value u
  have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu2
  rw [show 2 / (g * classBudgetW (fejerThetaOne theta gamma k) k) = 2 / g * (classBudgetW (fejerThetaOne theta gamma k) k)⁻¹ by
    field_simp]
  calc 2 / g * (classBudgetW (fejerThetaOne theta gamma k) k)⁻¹
      ≤ u ^ (32 * fejerProductExponent k + 1) * u ^ (32 * fejerProductExponent k) :=
        mul_le_mul hgi hbi (inv_pos.mpr hb).le (pow_nonneg hupos.le _)
    _ = u ^ (32 * fejerProductExponent k + 1 + 32 * fejerProductExponent k) := by rw [← pow_add]
    _ = u ^ (fejerStepP k + 1) := by
        congr 1
        unfold fejerStepP
        ring

theorem twoDiv_delta_le_fejer {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    2 / (section16Delta (fejerThetaOne theta gamma k) * classBudgetW (fejerThetaOne theta gamma k) k) ≤
      (2 / (gamma * theta)) ^ (fejerStepP k + 1) := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨-, -, hd, -⟩ := section16_theta_delta_bounds_with (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
  have hdi := classDeltaW_fejer_inv_le k hg hg1 ht ht1
  refine twoDiv_budget_le_fejer k hg hg1 ht ht1 hd ?_
  rw [div_eq_mul_inv, pow_succ, mul_comm]
  exact mul_le_mul hdi hu2 (by norm_num) (pow_nonneg (by linarith) _)

theorem twoDiv_gamma_le_fejer {gamma theta : Real} (k : Nat) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    2 / (gamma * classBudgetW (fejerThetaOne theta gamma k) k) ≤ (2 / (gamma * theta)) ^ (fejerStepP k + 1) := by
  obtain ⟨hu2, -, h2g, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  refine twoDiv_budget_le_fejer k hg hg1 ht ht1 hg ?_
  have hu1 : 1 ≤ 2 / (gamma * theta) := le_trans (by norm_num) hu2
  refine h2g.trans ?_
  calc 2 / (gamma * theta) = (2 / (gamma * theta)) ^ 1 := (pow_one _).symm
    _ ≤ _ := pow_le_pow_right₀ hu1 (Nat.le_add_left 1 _)

/-! ### The count -/

/-- **The count of the next class.** -/
theorem step_count_le_fejer {k D : Nat} (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    max (famPieceGraphBound (classQr V D k (n * classPiecesFejer gamma theta k) (classBudgetW (fejerThetaOne theta gamma k) k) gamma)
        (classPb V D (n * classPiecesFejer gamma theta k) (classBudgetW (fejerThetaOne theta gamma k) k) gamma)
        (n * classPiecesFejer gamma theta k) rho)
      (((3 ^ (k + 1) * (n * classPiecesFejer gamma theta k)) : Nat) : Real) ≤
      uniformBase V' n theta gamma rho ^ fejerStepCountDeg k D :=
  step_count_le_W hD hV hVV hg hg1 ht ht1 hr hr1 n (P := fejerStepP k)
    (classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1
      (fejerThetaOne_bounds k ht ht1 hg hg1).2).1
    (classPiecesFejer_le_gen k hg hg1 ht ht1) (twoDiv_gamma_le_fejer k hg hg1 ht ht1)
    (by have := fejerStepP_ge k; omega)

/-! ### The width exponent -/

/-- **The width exponent of the next class.** -/
theorem step_exp_inv_le_fejer {k D : Nat} (hD : 1 ≤ D) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p) (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V')
    {theta gamma rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hr : 0 < rho) (hr1 : rho ≤ 1) (n : Nat) :
    let M := n * classPiecesFejer gamma theta k
    let tS := classBudgetW (fejerThetaOne theta gamma k) k
    let gS := section16Delta (fejerThetaOne theta gamma k)
    let e := section16CappedWidthExponent
        (pieceLineExponent (familyWidthDivisor k p) (classQb V D M tS gS) (classEb V D M tS gS)
            (classEr V D k M tS gamma) rho *
          famPieceSliceExponent (classQr V D k M tS gamma) (classEs V D M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale (familyWidthPrefactor K) (classQb V D M tS gS) (tightZeta (fejerThetaOne theta gamma k / 4)) rho)
          (pieceLineExponent (familyWidthDivisor k p) (classQb V D M tS gS) (classEb V D M tS gS)
            (classEr V D k M tS gamma) rho)
          (famPieceSliceExponent (classQr V D k M tS gamma) (classEs V D M tS gamma) M rho))
    0 < e ∧ e⁻¹ ≤ uniformBase V' n theta gamma rho ^ fejerStepExpDeg k D :=
  have hf := fejerThetaOne_bounds k ht ht1 hg hg1
  have hb := classBudgetW_pos_le k hf.1 hf.2
  have hd := section16_theta_delta_bounds_with hf.1 hf.2
  step_exp_inv_le_W hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n (P := fejerStepP k)
    (T := fejerStepT k) hb.1 hb.2 hd.2.2.1 hd.2.2.2 (tightZeta_fejer_inv_le_gen k hg hg1 ht ht1)
    (classPiecesFejer_le_gen k hg hg1 ht ht1) (twoDiv_gamma_le_fejer k hg hg1 ht ht1)
    (twoDiv_delta_le_fejer k hg hg1 ht ht1) (by have := fejerStepP_ge k; omega)

/-! ### The threshold -/

theorem step_thr_le_fejer {k D : Nat} (hk : 1 ≤ k) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    classStepThresholdFejer V D theta gamma k ≤ (V' * (2 / (gamma * theta))) ^ fejerStepThrDeg k D := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hL := fejerProductThreshold_le_gen hk hg hg1 ht ht1
  have hgd := twoDiv_gamma_le_fejer k hg hg1 ht ht1
  have hdd := twoDiv_delta_le_fejer k hg hg1 ht ht1
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
  have hpiece : ∀ g : Real, 0 < g → 2 / (g * classBudgetW (fejerThetaOne theta gamma k) k) ≤ u ^ (fejerStepP k + 1) →
      (V * (2 / (g * classBudgetW (fejerThetaOne theta gamma k) k))) ^ D ≤ (V' * u) ^ fejerStepThrDeg k D := by
    intro g hg0 hgi
    have h1 : V * (2 / (g * classBudgetW (fejerThetaOne theta gamma k) k)) ≤ (V' * u) ^ (fejerStepP k + 1 + 1) :=
      (mul_le_mul_of_nonneg_left hgi (by linarith)).trans (hpow _)
    have h0 : 0 ≤ V * (2 / (g * classBudgetW (fejerThetaOne theta gamma k) k)) := by
      obtain ⟨hb, -⟩ := classBudgetW_pos_le k (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
      have : 0 < g * classBudgetW (fejerThetaOne theta gamma k) k := mul_pos hg0 hb
      exact mul_nonneg (by linarith) (div_nonneg (by norm_num) this.le)
    have h2 := pow_le_pow_left₀ h0 h1 D
    rw [← pow_mul] at h2
    refine h2.trans (pow_le_pow_right₀ ha1 ?_)
    unfold fejerStepThrDeg
    have : (fejerStepP k + 1 + 1) * D = D * (fejerStepP k + 2) := by ring
    omega
  unfold classStepThresholdFejer classPieceThresholdW
  refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
  · have h3 : (3 : Real) ≤ (V' * u) ^ 2 := by nlinarith only [ha2]
    exact h3.trans (pow_le_pow_right₀ ha1 (by unfold fejerStepThrDeg; omega))
  · refine hL.trans ((pow_le_pow_left₀ (by linarith) hua _).trans (pow_le_pow_right₀ ha1 ?_))
    unfold fejerStepThrDeg
    omega
  · obtain ⟨-, -, hd, -⟩ := section16_theta_delta_bounds_with (fejerThetaOne_bounds k ht ht1 hg hg1).1 (fejerThetaOne_bounds k ht ht1 hg hg1).2
    exact hpiece _ hd hdd
  · exact hpiece _ hg hgd

/-! ### The step -/

/-- **The step of route (II).** A uniform class of dimension `k ≥ 1` at one
degree `D`, with the family Lemma 16.6 at dimension `k`, gives a uniform class
of dimension `k+1`. -/
theorem powerUniformClass_succ_fejer {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V) {D : Nat}
    (hD : 1 ≤ D) (C : PowerUniformClass k V D D D) {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    Nonempty (PowerUniformClass (k + 1) V' (fejerStepCountDeg k D) (fejerStepExpDeg k D) (fejerStepThrDeg k D)) := by
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
    have hN' : classStepThresholdFejer V D theta gamma k ≤ N :=
      (step_thr_le_fejer hk hV hVV hg hg1 ht ht1).trans hN
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp_fejer C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover_fejer C hk hV (familyWidthPrefactor_pos hK) (familyWidthDivisor_pos hp)
      hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      exact step_count_le_fejer hD hV hVV hg hg1 ht ht1 hr hr1 n
    · intro rho hr hr1
      have h2 := uniformBase_two_le (hV.trans hVV) n ht ht1 hg hg1 hr hr1
      positivity
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := step_exp_inv_le_fejer hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      have := inv_anti₀ (inv_pos.mpr he0) hei
      rwa [inv_inv] at this
end LeanProofs.GowersSzemeredi
