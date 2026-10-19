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

* `powerUniformClass_succ_fejer`: **the Fejér step of route (II)**.

`fejerStepCountDeg`, `fejerStepExpDeg`, `powerUniformClass_succ_fejer`,
`step_count_le_fejer` and `step_exp_inv_le_fejer` are in
`Proofs16ClassStepDegreesFejerSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The degrees -/

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

/-! ### The threshold -/

theorem step_thr_le_fejer {k D : Nat} (hk : 1 ≤ k) {V V' : Real} (hV : 1 ≤ V) (hVV : V ≤ V')
    {theta gamma : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    classStepThresholdFejer V D theta gamma k ≤ (V' * (2 / (gamma * theta))) ^ fejerStepThrDeg k D := by
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  obtain ⟨ha0, haS⟩ := fejerThetaOne_bounds k ht ht1 hg hg1
  obtain ⟨hb, -⟩ := classBudgetW_pos_le k ha0 haS
  obtain ⟨-, -, hd, -⟩ := section16_theta_delta_bounds_with ha0 haS
  have hL := fejerProductThreshold_le_gen hk hg hg1 ht ht1
  have hgd := twoDiv_gamma_le_fejer k hg hg1 ht ht1
  have hdd := twoDiv_delta_le_fejer k hg hg1 ht ht1
  set u := 2 / (gamma * theta)
  have hV' : 1 ≤ V' := hV.trans hVV
  have hua : u ≤ V' * u := le_mul_of_one_le_left (by positivity) hV'
  have hVa : V ≤ V' * u := hVV.trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have ha2 : 2 ≤ V' * u := hu2.trans hua
  have ha1 : 1 ≤ V' * u := by linarith
  -- a piece `V * x` with `x ≤ u^(P+1)` is at most `(V'u)^(P+2)`
  have hpiece (x : Real) (hx0 : 0 ≤ x) (hx : x ≤ u ^ (fejerStepP k + 1)) :
      (V * x) ^ D ≤ (V' * u) ^ fejerStepThrDeg k D :=
    calc (V * x) ^ D ≤ (V' * u * (V' * u) ^ (fejerStepP k + 1)) ^ D := by
          gcongr; exact hx.trans (by gcongr)
      _ = (V' * u) ^ (D * (fejerStepP k + 2)) := by ring
      _ ≤ _ := pow_le_pow_right₀ ha1 (by unfold fejerStepThrDeg; omega)
  unfold classStepThresholdFejer classPieceThresholdW
  refine max_le ?_ (max_le ?_
    (max_le (hpiece _ (by positivity) hdd) (hpiece _ (by positivity) hgd)))
  · exact (show (3 : Real) ≤ (V' * u) ^ 2 by nlinarith only [ha2]).trans
      (pow_le_pow_right₀ ha1 (by unfold fejerStepThrDeg; omega))
  · exact hL.trans ((pow_le_pow_left₀ (by positivity) hua _).trans
      (pow_le_pow_right₀ ha1 (by unfold fejerStepThrDeg; omega)))

end LeanProofs.GowersSzemeredi
