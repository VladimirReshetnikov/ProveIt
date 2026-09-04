import FabiusFunction.QGamma

/-!
# The `q`-multiplication formula for `Γ_q`

For an integer `m ≥ 1`, `0 < q < 1`, and `x > 0`,

`Γ_q(mx) ∏_{j=1}^{m-1} Γ_{q^m}(j/m) = [m]_q^{mx-1} ∏_{j=0}^{m-1} Γ_{q^m}(x + j/m)`,

where `[m]_q = (1-q^m)/(1-q)`.  The two products of infinite symbols collapse by dissection:
`∏_{j<m} (q^{mx+j};q^m)_∞ = (q^{mx};q)_∞` and `∏_{j=1}^{m-1} (q^j;q^m)_∞ = (q;q)_∞/(q^m;q^m)_∞`;
the powers of `1-q^m` combine through `∑_{j<m} (1 - x - j/m) = m - mx - (m-1)/2`, and the
identity reduces to `((1-q^m)/(1-q))^{mx-1} (1-q^m)^{m-mx-(m-1)/2} = (1-q)^{1-mx} (1-q^m)^{(m-1)/2}`.

## Main declarations

* `prod_qPochhammerInfIn_pow_rpow`, `prod_qPochhammerInfIn_pow_succ`: the two dissections.
* `qGamma_multiplication`: the formula.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

variable {q : ℝ}

/-- `∑_{j<m} j = m(m-1)/2` in `ℝ`. -/
theorem sum_range_cast_eq (m : ℕ) : ∑ j ∈ range m, (j : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring

/-- The base `(q^m)^{x + j/m} = q^{mx} q^j`. -/
theorem pow_rpow_add_div (hq0 : 0 < q) {m : ℕ} (hm : 0 < m) (x : ℝ) (j : ℕ) :
    (q ^ m) ^ (x + j / m) = q ^ ((m : ℝ) * x) * q ^ j := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Real.rpow_natCast q m, ← Real.rpow_mul hq0.le, mul_add,
    show (m : ℝ) * ((j : ℝ) / m) = j by field_simp, Real.rpow_add hq0, Real.rpow_natCast]

/-- **Dissection of the shifted product**: `∏_{j<m} ((q^m)^{x+j/m}; q^m)_∞ = (q^{mx};q)_∞`. -/
theorem prod_qPochhammerInfIn_pow_rpow (hq0 : 0 < q) (hq1 : q < 1) {m : ℕ} (hm : 0 < m)
    (x : ℝ) :
    ∏ j ∈ range m, qPochhammerInfIn ((q ^ m) ^ (x + j / m)) (q ^ m) =
      qPochhammerInfIn (q ^ ((m : ℝ) * x)) q := by
  have hq : ‖q‖ < 1 := norm_lt_one_of_pos_of_lt_one hq0 hq1
  rw [qPochhammerInfIn_dissection (q ^ ((m : ℝ) * x)) hq hm]
  exact prod_congr rfl fun j _ => by rw [pow_rpow_add_div hq0 hm x j]

/-- **Dissection of `(q;q)_∞`**: `∏_{j<m-1} (q^{j+1};q^m)_∞ = (q;q)_∞ / (q^m;q^m)_∞`. -/
theorem prod_qPochhammerInfIn_pow_succ (hq0 : 0 < q) (hq1 : q < 1) {m : ℕ} (hm : 0 < m) :
    ∏ j ∈ range (m - 1), qPochhammerInfIn (q ^ (j + 1)) (q ^ m) =
      qPochhammerInfIn q q / qPochhammerInfIn (q ^ m) (q ^ m) := by
  have hq : ‖q‖ < 1 := norm_lt_one_of_pos_of_lt_one hq0 hq1
  have hqm0 : 0 < q ^ m := pow_pos hq0 m
  have hqm1 : q ^ m < 1 := pow_lt_one₀ hq0.le hq1 hm.ne'
  have hne : qPochhammerInfIn (q ^ m) (q ^ m) ≠ 0 := (qPochhammerInfIn_self_pos hqm0 hqm1).ne'
  rw [eq_div_iff hne, qPochhammerInfIn_dissection q hq hm]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel, prod_range_succ]
  congr 1
  · exact prod_congr rfl fun j _ => by rw [pow_succ']
  · rw [← pow_succ']

/-- **The `q`-multiplication formula**:
`Γ_q(mx) ∏_{j=1}^{m-1} Γ_{q^m}(j/m) = [m]_q^{mx-1} ∏_{j=0}^{m-1} Γ_{q^m}(x + j/m)`. -/
theorem qGamma_multiplication (hq0 : 0 < q) (hq1 : q < 1) {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx : 0 < x) :
    qGamma q (m * x) * ∏ j ∈ range (m - 1), qGamma (q ^ m) ((j + 1) / m) =
      qNumber q m ^ ((m : ℝ) * x - 1) * ∏ j ∈ range m, qGamma (q ^ m) (x + j / m) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hqm0 : 0 < q ^ m := pow_pos hq0 m
  have hqm1 : q ^ m < 1 := pow_lt_one₀ hq0.le hq1 hm.ne'
  have hA : 0 < 1 - q := by linarith
  have hB : 0 < 1 - q ^ m := by linarith
  have hP : 0 < qPochhammerInfIn q q := qPochhammerInfIn_self_pos hq0 hq1
  have hPm : 0 < qPochhammerInfIn (q ^ m) (q ^ m) := qPochhammerInfIn_self_pos hqm0 hqm1
  have hPmx : 0 < qPochhammerInfIn (q ^ ((m : ℝ) * x)) q :=
    qPochhammerInfIn_rpow_pos hq0 hq1 (by positivity)
  -- the two products of `q`-gamma values
  have hprod₁ : ∏ j ∈ range (m - 1), qGamma (q ^ m) ((j + 1) / m) =
      qPochhammerInfIn (q ^ m) (q ^ m) ^ (m - 1) /
          (qPochhammerInfIn q q / qPochhammerInfIn (q ^ m) (q ^ m)) *
        (1 - q ^ m) ^ (((m : ℝ) - 1) / 2) := by
    simp only [qGamma]
    rw [prod_mul_distrib, prod_div_distrib, prod_const, card_range,
      ← Real.rpow_sum_of_pos hB]
    have h1 : ∏ j ∈ range (m - 1), qPochhammerInfIn ((q ^ m) ^ (((j : ℝ) + 1) / m)) (q ^ m) =
        qPochhammerInfIn q q / qPochhammerInfIn (q ^ m) (q ^ m) := by
      rw [← prod_qPochhammerInfIn_pow_succ hq0 hq1 hm]
      refine prod_congr rfl fun j _ => ?_
      rw [← Real.rpow_natCast q m, ← Real.rpow_mul hq0.le,
        show (m : ℝ) * (((j : ℝ) + 1) / m) = ((j + 1 : ℕ) : ℝ) by push_cast; field_simp,
        Real.rpow_natCast q (j + 1)]
    have h2 : ∑ j ∈ range (m - 1), (1 - ((j : ℝ) + 1) / m) = ((m : ℝ) - 1) / 2 := by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      rw [Nat.add_sub_cancel, sum_sub_distrib, sum_const, card_range, ← sum_div,
        sum_add_distrib, sum_range_cast_eq, sum_const, card_range, nsmul_eq_mul]
      push_cast at hm0 ⊢
      field_simp
      ring
    rw [h1, h2]
  have hprod₂ : ∏ j ∈ range m, qGamma (q ^ m) (x + j / m) =
      qPochhammerInfIn (q ^ m) (q ^ m) ^ m / qPochhammerInfIn (q ^ ((m : ℝ) * x)) q *
        (1 - q ^ m) ^ ((m : ℝ) - m * x - ((m : ℝ) - 1) / 2) := by
    simp only [qGamma]
    rw [prod_mul_distrib, prod_div_distrib, prod_const, card_range,
      ← Real.rpow_sum_of_pos hB, prod_qPochhammerInfIn_pow_rpow hq0 hq1 hm x]
    have h2 : ∑ j ∈ range m, (1 - (x + (j : ℝ) / m)) = (m : ℝ) - m * x - ((m : ℝ) - 1) / 2 := by
      rw [sum_sub_distrib, sum_const, card_range, sum_add_distrib, sum_const, card_range,
        ← sum_div, sum_range_cast_eq, nsmul_eq_mul, nsmul_eq_mul]
      field_simp
      ring
    rw [h2]
  -- the powers of `1 - q` and `1 - q^m`
  have hAB : qNumber q m ^ ((m : ℝ) * x - 1) * (1 - q ^ m) ^ ((m : ℝ) - m * x - ((m : ℝ) - 1) / 2) =
      (1 - q) ^ (1 - (m : ℝ) * x) * (1 - q ^ m) ^ (((m : ℝ) - 1) / 2) := by
    rw [qNumber, Real.rpow_natCast, Real.div_rpow hB.le hA.le, div_mul_eq_mul_div,
      ← Real.rpow_add hB, show (m : ℝ) * x - 1 + ((m : ℝ) - m * x - ((m : ℝ) - 1) / 2) =
        ((m : ℝ) - 1) / 2 by ring, div_eq_mul_inv, ← Real.rpow_neg hA.le,
      show -((m : ℝ) * x - 1) = 1 - (m : ℝ) * x by ring, mul_comm]
  rw [hprod₁, hprod₂, show qNumber q m ^ ((m : ℝ) * x - 1) *
      (qPochhammerInfIn (q ^ m) (q ^ m) ^ m / qPochhammerInfIn (q ^ ((m : ℝ) * x)) q *
        (1 - q ^ m) ^ ((m : ℝ) - m * x - ((m : ℝ) - 1) / 2)) =
      qNumber q m ^ ((m : ℝ) * x - 1) * (1 - q ^ m) ^ ((m : ℝ) - m * x - ((m : ℝ) - 1) / 2) *
        (qPochhammerInfIn (q ^ m) (q ^ m) ^ m / qPochhammerInfIn (q ^ ((m : ℝ) * x)) q) by ring,
    hAB]
  unfold qGamma
  have hP' := hP.ne'
  have hPm' := hPm.ne'
  have hPmx' := hPmx.ne'
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  field_simp
  all_goals ring

end Fabius
