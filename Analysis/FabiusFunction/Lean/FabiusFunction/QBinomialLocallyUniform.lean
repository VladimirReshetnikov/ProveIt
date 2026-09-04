import FabiusFunction.QBinomialTheoremInfinite
import FabiusFunction.QPochhammerInfiniteBounds
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Local uniformity of the infinite `q`-binomial theorem

The series `∑_n (a;q)_n/(q;q)_n z^n` converges uniformly on every product of closed discs
`‖a‖ ≤ A`, `‖z‖ ≤ r < 1` (`tendstoUniformlyOn_qBinomial_closedBall`), by the Weierstrass
M-test with the majorant `(-A;‖q‖)_∞/(‖q‖;‖q‖)_∞ · r^n`, hence on every compact subset of
`𝕜 × {‖z‖ < 1}` (`tendstoUniformlyOn_qBinomial_of_isCompact`), and the sum is
`(az;q)_∞/(z;q)_∞` (`hasSum_qBinomial_theorem`).

## Main declarations

* `norm_qBinomial_term_le`.
* `tendstoUniformlyOn_qBinomial_closedBall`, `tendstoUniformlyOn_qBinomial_of_isCompact`.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
/-- The uniform bound of the terms of the `q`-binomial series on `‖a‖ ≤ A`, `‖z‖ ≤ r`.  The
numerator is bounded by `‖(a;q)_n‖ ≤ (-‖a‖;‖q‖)_∞ ≤ (-A;‖q‖)_∞`
(`norm_finiteQPochhammerIn_le`, `qPochhammerInfIn_neg_le_neg`); the hypothesis `0 ≤ A` is
implied by `‖a‖ ≤ A` and is kept only for the signature. -/
theorem norm_qBinomial_term_le {q : 𝕜} (hq : ‖q‖ < 1) {A r : ℝ} (_hA : 0 ≤ A) {a z : 𝕜}
    (ha : ‖a‖ ≤ A) (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖finiteQPochhammerIn a q n / finiteQPochhammerIn q q n * z ^ n‖ ≤
      qPochhammerInfIn (-A) ‖q‖ / qPochhammerInfIn ‖q‖ ‖q‖ * r ^ n := by
  have hq1 : ‖q‖ < 1 := hq
  have hP : 0 < qPochhammerInfIn ‖q‖ ‖q‖ :=
    qPochhammerInfIn_pos_of_lt_one (norm_nonneg q) hq1 (norm_nonneg q) hq1
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  -- the numerator: ‖(a;q)_n‖ ≤ (-‖a‖;‖q‖)_∞ ≤ (-A;‖q‖)_∞
  have hnum : ‖finiteQPochhammerIn a q n‖ ≤ qPochhammerInfIn (-A) ‖q‖ :=
    (norm_finiteQPochhammerIn_le a hq n).trans
      (qPochhammerInfIn_neg_le_neg (norm_nonneg a) ha (norm_nonneg q) hq1)
  have hden : qPochhammerInfIn ‖q‖ ‖q‖ ≤ ‖finiteQPochhammerIn q q n‖ :=
    qPochhammerInfIn_norm_le_norm_finiteQPochhammerIn q hq1.le hq n
  rw [norm_mul, norm_div, norm_pow]
  have hzn : ‖z‖ ^ n ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg z) hz n
  exact mul_le_mul (div_le_div₀ ((norm_nonneg _).trans hnum) hnum hP hden) hzn
    (by positivity) (div_nonneg ((norm_nonneg _).trans hnum) hP.le)

/-- **Uniform convergence on products of closed discs**: for `‖q‖ < 1`, `0 ≤ A` and
`0 ≤ r < 1`, the partial sums of `∑_n (a;q)_n/(q;q)_n z^n` converge uniformly to
`(az;q)_∞/(z;q)_∞` on `{‖a‖ ≤ A} × {‖z‖ ≤ r}`. -/
theorem tendstoUniformlyOn_qBinomial_closedBall {q : 𝕜} (hq : ‖q‖ < 1) {A r : ℝ} (hA : 0 ≤ A)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    TendstoUniformlyOn
      (fun (t : Finset ℕ) (p : 𝕜 × 𝕜) =>
        ∑ n ∈ t, finiteQPochhammerIn p.1 q n / finiteQPochhammerIn q q n * p.2 ^ n)
      (fun p => qPochhammerInfIn (p.1 * p.2) q / qPochhammerInfIn p.2 q) atTop
      (Metric.closedBall (0 : 𝕜) A ×ˢ Metric.closedBall (0 : 𝕜) r) := by
  have hu : Summable fun n : ℕ => qPochhammerInfIn (-A) ‖q‖ / qPochhammerInfIn ‖q‖ ‖q‖ * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have h := tendstoUniformlyOn_tsum (F := 𝕜)
    (f := fun n (p : 𝕜 × 𝕜) => finiteQPochhammerIn p.1 q n / finiteQPochhammerIn q q n * p.2 ^ n)
    hu (s := Metric.closedBall (0 : 𝕜) A ×ˢ Metric.closedBall (0 : 𝕜) r) fun n p hp => by
      rw [Set.mem_prod, Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right,
        dist_zero_right] at hp
      exact norm_qBinomial_term_le hq hA hp.1 hp.2 n
  refine h.congr_right fun p hp => ?_
  rw [Set.mem_prod, Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right,
    dist_zero_right] at hp
  exact (hasSum_qBinomial_theorem hq p.1 (lt_of_le_of_lt hp.2 hr1)).tsum_eq

/-- **Local uniformity of the infinite `q`-binomial theorem**: the convergence is uniform on
every compact subset of `𝕜 × {‖z‖ < 1}`. -/
theorem tendstoUniformlyOn_qBinomial_of_isCompact {q : 𝕜} (hq : ‖q‖ < 1) {K : Set (𝕜 × 𝕜)}
    (hK : IsCompact K) (hK1 : ∀ p ∈ K, ‖p.2‖ < 1) :
    TendstoUniformlyOn
      (fun (t : Finset ℕ) (p : 𝕜 × 𝕜) =>
        ∑ n ∈ t, finiteQPochhammerIn p.1 q n / finiteQPochhammerIn q q n * p.2 ^ n)
      (fun p => qPochhammerInfIn (p.1 * p.2) q / qPochhammerInfIn p.2 q) atTop K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  -- a bound `A` for the first coordinate
  obtain ⟨A, hA⟩ := (Metric.isBounded_iff_subset_closedBall (0 : 𝕜 × 𝕜)).mp hK.isBounded
  -- the maximum of `‖p.2‖` on `K` is `r < 1`
  obtain ⟨p₀, hp₀, hmax⟩ := hK.exists_isMaxOn hne
    (continuous_norm.comp continuous_snd).continuousOn
  set r := ‖p₀.2‖ with hr
  have hr1 : r < 1 := hK1 p₀ hp₀
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (mem_closedBall_zero_iff.mp (hA hp₀))
  refine (tendstoUniformlyOn_qBinomial_closedBall hq hA0 (norm_nonneg _) hr1).mono fun p hp => ?_
  rw [Set.mem_prod, Metric.mem_closedBall, Metric.mem_closedBall, dist_zero_right, dist_zero_right]
  refine ⟨?_, hmax hp⟩
  have := mem_closedBall_zero_iff.mp (hA hp)
  calc ‖p.1‖ ≤ max ‖p.1‖ ‖p.2‖ := le_max_left _ _
    _ = ‖p‖ := (Prod.norm_def p).symm
    _ ≤ A := this

end Fabius
