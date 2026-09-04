import FabiusFunction.QGaussSummation
import FabiusFunction.QBinomialCauchy
import FabiusFunction.QBinomialTheoremInfinite

/-!
# The `q`-Gauss summation on its full domain

`₂φ₁(a, b; c; q, c/(ab)) = (c/a;q)_∞ (c/b;q)_∞ / ((c;q)_∞ (c/(ab);q)_∞)` for `‖q‖ < 1`,
`a, b ≠ 0`, `(c;q)_∞ ≠ 0` and `‖c/(ab)‖ < 1` — no restriction on `‖b‖`, and no hypothesis on
`(c/b;q)_∞`.

`QGaussSummation` proves this on the smaller domain `‖b‖ < 1` from Heine's transformation.
Here the full domain is reached without analytic continuation: the `q`-Pfaff–Saalschütz sum
in its Cauchy form (`finite_qCauchy_second_identity` at `c ↦ c/(ab)`, divided by
`(c;q)_n (c/(ab);q)_n`),

`∑_{k ≤ n} [n,k]_q (a;q)_k (b;q)_k z^k (z;q)_{n-k} (cq^k;q)_{n-k} / ((c;q)_n (z;q)_n)
  = (c/a;q)_n (c/b;q)_n / ((c;q)_n (z;q)_n)`,   `z = c/(ab)`,

is a double family whose `k`-th column converges to the `k`-th term of `₂φ₁(a,b;c;q,z)` and
whose rows are dominated by one geometric series in `‖z‖`; Tannery's theorem
(`hasSum_of_tendsto_of_dominated`) then gives the sum, exactly as the infinite `q`-binomial
theorem was obtained from the first finite Cauchy identity.  Valid in every complete normed
field.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The `q`-Gauss summation, full domain** (thm:q-gauss): for `‖q‖ < 1`, `a, b ≠ 0`,
`(c;q)_∞ ≠ 0` and `‖c/(ab)‖ < 1`,
`∑_k (a;q)_k (b;q)_k / ((q;q)_k (c;q)_k) (c/(ab))^k
  = (c/a;q)_∞ (c/b;q)_∞ / ((c;q)_∞ (c/(ab);q)_∞)`. -/
theorem hasSum_q_gauss {q : 𝕜} (hq : ‖q‖ < 1) {a b c : 𝕜} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc : qPochhammerInfIn c q ≠ 0) (hz : ‖c / (a * b)‖ < 1) :
    HasSum (twoPhiOneTerm a b c q (c / (a * b)))
      (qPochhammerInfIn (c / a) q * qPochhammerInfIn (c / b) q /
        (qPochhammerInfIn c q * qPochhammerInfIn (c / (a * b)) q)) := by
  set z := c / (a * b) with hz_def
  have hzinf : qPochhammerInfIn z q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hz
  have haz : a * z = c / b := by
    rw [hz_def, mul_div_assoc', mul_div_mul_left c b ha0]
  have hbz : b * z = c / a := by
    rw [hz_def, mul_div_assoc', mul_comm a b, mul_div_mul_left c a hb0]
  have habz : a * b * z = c := by
    rw [hz_def, mul_div_assoc', mul_div_cancel_left₀ c (mul_ne_zero ha0 hb0)]
  have hqinf : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hq
  -- nonnegative constants for the majorant
  have hgm : 0 ≤ gaussianMajorant q := gaussianMajorant_nonneg hq
  have hA : 0 ≤ qPochhammerInfIn (-‖a‖) ‖q‖ :=
    zero_le_one.trans (one_le_qPochhammerInfIn_neg (norm_nonneg a) (norm_nonneg q) hq)
  have hB : 0 ≤ qPochhammerInfIn (-‖b‖) ‖q‖ :=
    zero_le_one.trans (one_le_qPochhammerInfIn_neg (norm_nonneg b) (norm_nonneg q) hq)
  have hZ : 0 ≤ qPochhammerInfIn (-‖z‖) ‖q‖ :=
    zero_le_one.trans (one_le_qPochhammerInfIn_neg (norm_nonneg z) (norm_nonneg q) hq)
  have hC : 0 ≤ qPochhammerInfIn (-‖c‖) ‖q‖ :=
    zero_le_one.trans (one_le_qPochhammerInfIn_neg (norm_nonneg c) (norm_nonneg q) hq)
  have hKc : 0 ≤ qPochhammerInfIn (-‖c‖) ‖q‖ / ‖qPochhammerInfIn c q‖ :=
    div_nonneg hC (norm_nonneg _)
  have hKz : 0 ≤ qPochhammerInfIn (-‖z‖) ‖q‖ / ‖qPochhammerInfIn z q‖ :=
    div_nonneg hZ (norm_nonneg _)
  refine hasSum_of_tendsto_of_dominated
    (f := fun n k => gaussianBinomial q n k * finiteQPochhammerIn a q k *
      finiteQPochhammerIn b q k * z ^ k * finiteQPochhammerIn z q (n - k) *
      finiteQPochhammerIn (c * q ^ k) q (n - k) /
      (finiteQPochhammerIn c q n * finiteQPochhammerIn z q n))
    (bound := fun k => gaussianMajorant q * qPochhammerInfIn (-‖a‖) ‖q‖ *
      qPochhammerInfIn (-‖b‖) ‖q‖ * qPochhammerInfIn (-‖z‖) ‖q‖ *
      qPochhammerInfIn (-‖c‖) ‖q‖ * (qPochhammerInfIn (-‖c‖) ‖q‖ / ‖qPochhammerInfIn c q‖) *
      (qPochhammerInfIn (-‖z‖) ‖q‖ / ‖qPochhammerInfIn z q‖) * ‖z‖ ^ k)
    (S := fun n => finiteQPochhammerIn (c / a) q n * finiteQPochhammerIn (c / b) q n /
      (finiteQPochhammerIn c q n * finiteQPochhammerIn z q n))
    ?_ ?_ ?_ ?_ ?_
  · exact (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left _
  · intro k
    have hck : finiteQPochhammerIn c q k ≠ 0 :=
      finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero c hq hc k
    have hqk : finiteQPochhammerIn q q k ≠ 0 :=
      finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero q hq hqinf k
    have hcs := qPochhammerInfIn_eq_finite_mul_shift c hq k
    have hcqk : qPochhammerInfIn (c * q ^ k) q ≠ 0 := by
      rw [hcs] at hc
      exact right_ne_zero_of_mul hc
    have h1 := tendsto_gaussianBinomial_atTop hq k
    have h2 : Tendsto (fun n : ℕ => finiteQPochhammerIn z q (n - k)) atTop
        (𝓝 (qPochhammerInfIn z q)) :=
      (tendsto_finiteQPochhammerIn_qPochhammerInfIn z hq).comp (tendsto_sub_atTop_nat k)
    have h3 : Tendsto (fun n : ℕ => finiteQPochhammerIn (c * q ^ k) q (n - k)) atTop
        (𝓝 (qPochhammerInfIn (c * q ^ k) q)) :=
      (tendsto_finiteQPochhammerIn_qPochhammerInfIn (c * q ^ k) hq).comp
        (tendsto_sub_atTop_nat k)
    have h4 := tendsto_finiteQPochhammerIn_qPochhammerInfIn c hq
    have h5 := tendsto_finiteQPochhammerIn_qPochhammerInfIn z hq
    have h := (((((h1.mul_const (finiteQPochhammerIn a q k)).mul_const
      (finiteQPochhammerIn b q k)).mul_const (z ^ k)).mul h2).mul h3).div (h4.mul h5)
      (mul_ne_zero hc hzinf)
    have hval : (finiteQPochhammerIn q q k)⁻¹ * finiteQPochhammerIn a q k *
        finiteQPochhammerIn b q k * z ^ k * qPochhammerInfIn z q *
        qPochhammerInfIn (c * q ^ k) q / (qPochhammerInfIn c q * qPochhammerInfIn z q) =
        twoPhiOneTerm a b c q z k := by
      rw [twoPhiOneTerm, hcs]
      field_simp
    rw [hval] at h
    exact h
  · intro n k
    rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow,
      div_eq_mul_inv, mul_inv]
    have hG := norm_gaussianBinomial_le hq n k
    have ha := norm_finiteQPochhammerIn_le a hq k
    have hb := norm_finiteQPochhammerIn_le b hq k
    have hzk := norm_finiteQPochhammerIn_le z hq (n - k)
    have hck : ‖finiteQPochhammerIn (c * q ^ k) q (n - k)‖ ≤ qPochhammerInfIn (-‖c‖) ‖q‖ := by
      refine (norm_finiteQPochhammerIn_le _ hq _).trans
        (qPochhammerInfIn_neg_le_neg (norm_nonneg _) ?_ (norm_nonneg q) hq)
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (norm_nonneg c) (pow_le_one₀ (norm_nonneg q) hq.le)
    have hcn := inv_norm_finiteQPochhammerIn_le c hq hc n
    have hzn := inv_norm_finiteQPochhammerIn_le z hq hzinf n
    calc ‖gaussianBinomial q n k‖ * ‖finiteQPochhammerIn a q k‖ * ‖finiteQPochhammerIn b q k‖ *
          ‖z‖ ^ k * ‖finiteQPochhammerIn z q (n - k)‖ *
          ‖finiteQPochhammerIn (c * q ^ k) q (n - k)‖ *
          (‖finiteQPochhammerIn c q n‖⁻¹ * ‖finiteQPochhammerIn z q n‖⁻¹)
        ≤ gaussianMajorant q * qPochhammerInfIn (-‖a‖) ‖q‖ * qPochhammerInfIn (-‖b‖) ‖q‖ *
          ‖z‖ ^ k * qPochhammerInfIn (-‖z‖) ‖q‖ * qPochhammerInfIn (-‖c‖) ‖q‖ *
          ((qPochhammerInfIn (-‖c‖) ‖q‖ / ‖qPochhammerInfIn c q‖) *
            (qPochhammerInfIn (-‖z‖) ‖q‖ / ‖qPochhammerInfIn z q‖)) := by gcongr
      _ = _ := by ring
  · intro n
    have hsupp : ∀ k ∉ Finset.range (n + 1),
        gaussianBinomial q n k * finiteQPochhammerIn a q k * finiteQPochhammerIn b q k * z ^ k *
          finiteQPochhammerIn z q (n - k) * finiteQPochhammerIn (c * q ^ k) q (n - k) /
          (finiteQPochhammerIn c q n * finiteQPochhammerIn z q n) = 0 := by
      intro k hk
      rw [Finset.mem_range, not_lt] at hk
      rw [gaussianBinomial_eq_zero_of_lt q hk]
      ring
    have hfin : ∑ k ∈ Finset.range (n + 1),
        gaussianBinomial q n k * finiteQPochhammerIn a q k * finiteQPochhammerIn b q k * z ^ k *
          finiteQPochhammerIn z q (n - k) * finiteQPochhammerIn (c * q ^ k) q (n - k) /
          (finiteQPochhammerIn c q n * finiteQPochhammerIn z q n) =
        finiteQPochhammerIn (c / a) q n * finiteQPochhammerIn (c / b) q n /
          (finiteQPochhammerIn c q n * finiteQPochhammerIn z q n) := by
      have hC := finite_qCauchy_second_identity q a b z n
      rw [haz, hbz] at hC
      simp only [habz] at hC
      rw [mul_comm (finiteQPochhammerIn (c / a) q n), hC, Finset.sum_div]
    rw [← hfin]
    exact hasSum_sum_of_ne_finset_zero hsupp
  · exact ((tendsto_finiteQPochhammerIn_qPochhammerInfIn (c / a) hq).mul
      (tendsto_finiteQPochhammerIn_qPochhammerInfIn (c / b) hq)).div
      ((tendsto_finiteQPochhammerIn_qPochhammerInfIn c hq).mul
        (tendsto_finiteQPochhammerIn_qPochhammerInfIn z hq)) (mul_ne_zero hc hzinf)

/-- **The `q`-Gauss summation, full domain**, as an identity for `₂φ₁`. -/
theorem q_gauss_summation_full {q : 𝕜} (hq : ‖q‖ < 1) {a b c : 𝕜} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc : qPochhammerInfIn c q ≠ 0) (hz : ‖c / (a * b)‖ < 1) :
    twoPhiOne a b c q (c / (a * b)) =
      qPochhammerInfIn (c / a) q * qPochhammerInfIn (c / b) q /
        (qPochhammerInfIn c q * qPochhammerInfIn (c / (a * b)) q) :=
  (hasSum_q_gauss hq ha0 hb0 hc hz).tsum_eq

/-- The `q`-Gauss series converges absolutely on the full domain. -/
theorem summable_q_gauss_term {q : 𝕜} (hq : ‖q‖ < 1) {a b c : 𝕜} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hc : qPochhammerInfIn c q ≠ 0) (hz : ‖c / (a * b)‖ < 1) :
    Summable (twoPhiOneTerm a b c q (c / (a * b))) :=
  (hasSum_q_gauss hq ha0 hb0 hc hz).summable

end Fabius
