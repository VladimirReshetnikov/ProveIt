import FabiusFunction.RogersRamanujan

/-!
# The Rogers–Ramanujan-type series `F_m` and Rogers' recurrence

`F_m(q) = ∑_{n ≥ 0} q^{n² + mn} / (q;q)_n` (`rogersSeries`), absolutely convergent for `‖q‖ < 1`
(`summable_rogersSeries_term`), with `F_0 = G`, `F_1 = H` the Rogers–Ramanujan functions
(`rogersSeries_zero_eq`, `rogersSeries_one_eq`), and Rogers' recurrence

  `F_m = F_{m+1} + q^{m+1} F_{m+2}`  (`rogersSeries_recurrence`, qg:lem-rogers-recurrence):

termwise `q^{n²+mn}(1 - q^n)/(q;q)_n = q^{n²+mn}/(q;q)_{n-1}` for `n ≥ 1`, and the shift
`n = r + 1` turns the exponent into `m + 1 + r² + (m+2) r`.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- `F_m(q) = ∑_n q^{n² + mn}/(q;q)_n`. -/
noncomputable def rogersSeries (q : 𝕜) (m : ℕ) : 𝕜 :=
  ∑' n : ℕ, q ^ (n * n + m * n) / finiteQPochhammerIn q q n

/-- The defining summand of the Rogers series is summable for `‖q‖ < 1`. -/
theorem summable_rogersSeries_term {q : 𝕜} (hq : ‖q‖ < 1) (m : ℕ) :
    Summable fun n : ℕ => q ^ (n * n + m * n) / finiteQPochhammerIn q q n := by
  have hQ : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_self_ne_zero hq
  set C₁ : ℝ := qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖ with hC₁def
  have hC : ∀ n, ‖finiteQPochhammerIn q q n‖⁻¹ ≤ C₁ := fun n =>
    inv_norm_finiteQPochhammerIn_le q hq hQ n
  refine Summable.of_norm_bounded (g := fun n : ℕ => C₁ * ‖q‖ ^ n)
    ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left C₁) fun n => ?_
  rw [norm_div, div_eq_mul_inv, norm_pow]
  calc ‖q‖ ^ (n * n + m * n) * ‖finiteQPochhammerIn q q n‖⁻¹ ≤ ‖q‖ ^ n * C₁ :=
        mul_le_mul (pow_le_pow_of_le_one (norm_nonneg q) hq.le (by nlinarith [Nat.le_mul_self n]))
          (hC n) (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = C₁ * ‖q‖ ^ n := mul_comm _ _

/-- The defining series converges to `rogersSeries q m`. -/
theorem hasSum_rogersSeries {q : 𝕜} (hq : ‖q‖ < 1) (m : ℕ) :
    HasSum (fun n : ℕ => q ^ (n * n + m * n) / finiteQPochhammerIn q q n) (rogersSeries q m) :=
  (summable_rogersSeries_term hq m).hasSum

/-- `F_0 = G`: the first Rogers–Ramanujan identity. -/
theorem rogersSeries_zero_eq {q : 𝕜} (hq : ‖q‖ < 1) :
    rogersSeries q 0 = (qPochhammerInfIn q (q ^ 5) * qPochhammerInfIn (q ^ 4) (q ^ 5))⁻¹ := by
  refine ((hasSum_rogersRamanujan_first hq).congr_fun fun n => ?_).tsum_eq
  simp

/-- `F_1 = H`: the second Rogers–Ramanujan identity. -/
theorem rogersSeries_one_eq {q : 𝕜} (hq : ‖q‖ < 1) :
    rogersSeries q 1 = (qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 3) (q ^ 5))⁻¹ := by
  refine ((hasSum_rogersRamanujan_second hq).congr_fun fun n => ?_).tsum_eq
  rw [show n * n + 1 * n = n * (n + 1) by ring]

/-- **Rogers' recurrence** (qg:lem-rogers-recurrence): `F_m = F_{m+1} + q^{m+1} F_{m+2}`. -/
theorem rogersSeries_recurrence {q : 𝕜} (hq : ‖q‖ < 1) (m : ℕ) :
    rogersSeries q m = rogersSeries q (m + 1) + q ^ (m + 1) * rogersSeries q (m + 2) := by
  have hq' : ∀ n, finiteQPochhammerIn q q n ≠ 0 := finiteQPochhammerIn_self_ne_zero hq
  set h : ℕ → 𝕜 := fun n => q ^ (n * n + m * n) / finiteQPochhammerIn q q n -
    q ^ (n * n + (m + 1) * n) / finiteQPochhammerIn q q n with hh
  have hh0 : h 0 = 0 := by simp [hh]
  have hhs : ∀ r, h (r + 1) = q ^ (m + 1) * (q ^ (r * r + (m + 2) * r) / finiteQPochhammerIn q q r) := by
    intro r
    have h1 := hq' r
    have h2 : (1 : 𝕜) - q * q ^ r ≠ 0 := by
      intro h0
      apply hq' (r + 1)
      rw [finiteQPochhammerIn_succ, h0, mul_zero]
    simp only [hh]
    rw [div_sub_div_same, finiteQPochhammerIn_succ, mul_div_assoc',
      div_eq_div_iff (mul_ne_zero h1 h2) h1]
    ring
  have hsum : HasSum h (q ^ (m + 1) * rogersSeries q (m + 2)) := by
    refine (hasSum_nat_add_iff' 1).mp ?_
    rw [sum_range_one, hh0, sub_zero]
    have := (hasSum_rogersSeries hq (m + 2)).mul_left (q ^ (m + 1))
    refine this.congr_fun fun r => ?_
    rw [hhs r]
  have hsub := (hasSum_rogersSeries hq m).sub (hasSum_rogersSeries hq (m + 1))
  have := hsub.unique hsum
  rw [sub_eq_iff_eq_add] at this
  rw [this]
  ring

end Fabius
