import FabiusFunction.BaileyPairs
import FabiusFunction.QPochhammerInfiniteBounds
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The limiting Bailey lemma, infinite form

For a Bailey pair `(α, β)` relative to `a` in a complete normed field with `‖q‖ < 1` and
`(aq;q)_∞ ≠ 0`, if both `∑ a^n q^{n²} α_n` and `∑ a^n q^{n²} β_n` converge absolutely, then

  `∑_{n ≥ 0} a^n q^{n²} β_n = (aq;q)_∞⁻¹ ∑_{n ≥ 0} a^n q^{n²} α_n`

(`IsBaileyPair.hasSum_limit`).  The transformed sequence `β'_N` of the finite limiting lemma
is a finite sum both in the `β_j` (by definition) and in the `α_r` (by the finite lemma);
Tannery's theorem, with the uniform bounds `‖(q;q)_m‖⁻¹ ≤ C₁`, `‖(aq;q)_m‖⁻¹ ≤ C₂` of
`inv_norm_finiteQPochhammerIn_le`, evaluates `lim β'_N` both ways, and the two limits agree.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The limiting Bailey lemma, infinite form** (cor:bailey-limit-infinite). -/
theorem IsBaileyPair.hasSum_limit {a q : 𝕜} (hq : ‖q‖ < 1) (ha : qPochhammerInfIn (a * q) q ≠ 0)
    {α β : ℕ → 𝕜} (h : IsBaileyPair a q α β)
    (hα : Summable fun n => ‖a ^ n * q ^ (n * n) * α n‖)
    (hβ : Summable fun n => ‖a ^ n * q ^ (n * n) * β n‖) :
    HasSum (fun n => a ^ n * q ^ (n * n) * β n)
      ((qPochhammerInfIn (a * q) q)⁻¹ * ∑' n, a ^ n * q ^ (n * n) * α n) := by
  have hQ : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_self_ne_zero hq
  have hqn : ∀ n, finiteQPochhammerIn q q n ≠ 0 := finiteQPochhammerIn_self_ne_zero hq
  have han : ∀ n, finiteQPochhammerIn (a * q) q n ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero (a * q) hq ha
  have h' := h.limit_step hqn han
  -- the uniform bounds on the reciprocals of the finite products
  set C₁ : ℝ := qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖ with hC₁def
  set C₂ : ℝ := qPochhammerInfIn (-‖a * q‖) ‖q‖ / ‖qPochhammerInfIn (a * q) q‖ with hC₂def
  have hC₁ : ∀ n, ‖finiteQPochhammerIn q q n‖⁻¹ ≤ C₁ := fun n =>
    inv_norm_finiteQPochhammerIn_le q hq hQ n
  have hC₂ : ∀ n, ‖finiteQPochhammerIn (a * q) q n‖⁻¹ ≤ C₂ := fun n =>
    inv_norm_finiteQPochhammerIn_le (a * q) hq ha n
  have hC₁0 : 0 ≤ C₁ := (inv_nonneg.mpr (norm_nonneg _)).trans (hC₁ 0)
  have hC₂0 : 0 ≤ C₂ := (inv_nonneg.mpr (norm_nonneg _)).trans (hC₂ 0)
  -- the transformed `β`
  set β' : ℕ → 𝕜 := fun N =>
    ∑ j ∈ range (N + 1), a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (N - j) * β j with hβ'
  have hβ'α : ∀ N, β' N = ∑ r ∈ range (N + 1), a ^ r * q ^ (r * r) * α r /
      (finiteQPochhammerIn q q (N - r) * finiteQPochhammerIn (a * q) q (N + r)) :=
    fun N => h' N
  -- (L) `β'_N → (q;q)_∞⁻¹ ∑ a^j q^{j²} β_j`
  let f : ℕ → ℕ → 𝕜 := fun N j =>
    if j ≤ N then a ^ j * q ^ (j * j) * β j / finiteQPochhammerIn q q (N - j) else 0
  have hfin : ∀ N, ∑' j, f N j = β' N := by
    intro N
    rw [tsum_eq_sum (s := range (N + 1)) (fun j hj => by
      simp only [f]
      rw [mem_range] at hj
      rw [if_neg (by omega)])]
    refine sum_congr rfl fun j hj => ?_
    simp only [f]
    rw [if_pos (Nat.lt_succ_iff.mp (mem_range.mp hj))]
    ring
  have hfb : ∀ N j, ‖f N j‖ ≤ ‖a ^ j * q ^ (j * j) * β j‖ * C₁ := by
    intro N j
    simp only [f]
    split_ifs
    · rw [norm_div, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (hC₁ _) (norm_nonneg _)
    · rw [norm_zero]
      positivity
  have hfpt : ∀ j, Tendsto (fun N => f N j) atTop
      (𝓝 (a ^ j * q ^ (j * j) * β j / qPochhammerInfIn q q)) := by
    intro j
    have h1 : Tendsto (fun N => finiteQPochhammerIn q q (N - j)) atTop
        (𝓝 (qPochhammerInfIn q q)) :=
      (tendsto_finiteQPochhammerIn_qPochhammerInfIn q hq).comp (tendsto_sub_atTop_nat j)
    have h2 := (tendsto_const_nhds (x := a ^ j * q ^ (j * j) * β j)).div h1 hQ
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop j] with N hN
    simp only [f]
    rw [if_pos hN]
    rfl
  have hL : Tendsto β' atTop
      (𝓝 (∑' j, a ^ j * q ^ (j * j) * β j / qPochhammerInfIn q q)) := by
    have := tendsto_tsum_of_dominated_convergence (hβ.mul_right C₁) hfpt (Eventually.of_forall hfb)
    simpa only [hfin] using this
  -- (R) `β'_N → ((q;q)_∞ (aq;q)_∞)⁻¹ ∑ a^r q^{r²} α_r`
  let g : ℕ → ℕ → 𝕜 := fun N r =>
    if r ≤ N then a ^ r * q ^ (r * r) * α r /
      (finiteQPochhammerIn q q (N - r) * finiteQPochhammerIn (a * q) q (N + r)) else 0
  have hgin : ∀ N, ∑' r, g N r = β' N := by
    intro N
    rw [tsum_eq_sum (s := range (N + 1)) (fun r hr => by
      simp only [g]
      rw [mem_range] at hr
      rw [if_neg (by omega)]), hβ'α N]
    refine sum_congr rfl fun r hr => ?_
    simp only [g]
    rw [if_pos (Nat.lt_succ_iff.mp (mem_range.mp hr))]
  have hgb : ∀ N r, ‖g N r‖ ≤ ‖a ^ r * q ^ (r * r) * α r‖ * (C₁ * C₂) := by
    intro N r
    simp only [g]
    split_ifs
    · rw [norm_div, div_eq_mul_inv, norm_mul (finiteQPochhammerIn q q (N - r)), mul_inv]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (hC₁ _) (hC₂ _) (inv_nonneg.mpr (norm_nonneg _)) hC₁0) (norm_nonneg _)
    · rw [norm_zero]
      positivity
  have hgpt : ∀ r, Tendsto (fun N => g N r) atTop
      (𝓝 (a ^ r * q ^ (r * r) * α r / (qPochhammerInfIn q q * qPochhammerInfIn (a * q) q))) := by
    intro r
    have h1 : Tendsto (fun N => finiteQPochhammerIn q q (N - r)) atTop
        (𝓝 (qPochhammerInfIn q q)) :=
      (tendsto_finiteQPochhammerIn_qPochhammerInfIn q hq).comp (tendsto_sub_atTop_nat r)
    have h3 : Tendsto (fun N => finiteQPochhammerIn (a * q) q (N + r)) atTop
        (𝓝 (qPochhammerInfIn (a * q) q)) :=
      (tendsto_finiteQPochhammerIn_qPochhammerInfIn (a * q) hq).comp (tendsto_add_atTop_nat r)
    have h2 := (tendsto_const_nhds (x := a ^ r * q ^ (r * r) * α r)).div (h1.mul h3)
      (mul_ne_zero hQ ha)
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop r] with N hN
    simp only [g]
    rw [if_pos hN]
    rfl
  have hR : Tendsto β' atTop
      (𝓝 (∑' r, a ^ r * q ^ (r * r) * α r /
        (qPochhammerInfIn q q * qPochhammerInfIn (a * q) q))) := by
    have := tendsto_tsum_of_dominated_convergence (hα.mul_right (C₁ * C₂)) hgpt
      (Eventually.of_forall hgb)
    simpa only [hgin] using this
  -- the two limits agree
  have heq := tendsto_nhds_unique hL hR
  rw [tsum_div_const, tsum_div_const] at heq
  have hsβ : Summable fun n => a ^ n * q ^ (n * n) * β n := hβ.of_norm
  have hval : ∑' n, a ^ n * q ^ (n * n) * β n =
      (qPochhammerInfIn (a * q) q)⁻¹ * ∑' n, a ^ n * q ^ (n * n) * α n := by
    rw [div_eq_div_iff hQ (mul_ne_zero hQ ha)] at heq
    calc ∑' n, a ^ n * q ^ (n * n) * β n
        = (∑' n, a ^ n * q ^ (n * n) * β n) * (qPochhammerInfIn q q * qPochhammerInfIn (a * q) q) /
            (qPochhammerInfIn q q * qPochhammerInfIn (a * q) q) := by
          field_simp
      _ = (∑' n, a ^ n * q ^ (n * n) * α n) * qPochhammerInfIn q q /
            (qPochhammerInfIn q q * qPochhammerInfIn (a * q) q) := by
          rw [heq]
      _ = (qPochhammerInfIn (a * q) q)⁻¹ * ∑' n, a ^ n * q ^ (n * n) * α n := by
          field_simp
  rw [← hval]
  exact hsβ.hasSum

end Fabius
