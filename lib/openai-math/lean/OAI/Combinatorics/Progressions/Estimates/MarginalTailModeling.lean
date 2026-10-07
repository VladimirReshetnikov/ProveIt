import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import OAI.Combinatorics.Progressions.Estimates.ConvexEmpiricalApproximation
import OAI.Combinatorics.Progressions.Linear.WeightedDualVector
import OAI.Combinatorics.Progressions.Probability.FiniteRelativeDensity

namespace OAI

section

namespace Erdos3

open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem exists_modeling_dual_obstruction (X : Seminorm ℂ E) {S : Set E}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) {R tau : ℝ} (hR : 0 < R) (htau : 0 < tau)
    (b : E) (hb : b ∉ closure (R • convexHull ℝ S + X.closedBall 0 tau)) :
    ∃ f : E →L[ℂ] ℂ, 1 < (f b).re ∧
      (∀ v, tau * ‖f v‖ ≤ X v) ∧ (∀ Q ∈ S, R * ‖f Q‖ < 1) := by
  let A : Set E := R • convexHull ℝ S + X.closedBall 0 tau
  have hconv : Convex ℝ A :=
    ((convex_convexHull ℝ S).smul R).add (X.convex_closedBall 0 tau)
  have hzS : (0 : E) ∈ convexHull ℝ S := subset_convexHull ℝ S (hS.zero_mem hSn)
  have hzR : (0 : E) ∈ R • convexHull ℝ S := by
    simpa only [smul_zero] using Set.smul_mem_smul_set (a := R) hzS
  have hzBall : (0 : E) ∈ X.closedBall 0 tau := X.mem_closedBall_self htau.le
  have hz : (0 : E) ∈ A := by
    simpa only [add_zero] using Set.add_mem_add hzR hzBall
  obtain ⟨g, u, hgu, hub⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := ℂ) hconv.closure isClosed_closure hb
  have hu : 0 < u := by simpa only [map_zero, Complex.zero_re] using hgu 0 (subset_closure hz)
  let f : E →L[ℂ] ℂ := (u⁻¹ : ℝ) • g
  have hf (v : E) : (f v).re = (g v).re / u := by
    change (u⁻¹ • g v).re = _
    rw [Complex.smul_re, smul_eq_mul]
    ring
  have hfb : 1 < (f b).re := by
    rw [hf]
    exact (lt_div_iff₀ hu).mpr (by simpa using hub)
  have hfa : ∀ v ∈ A, (f v).re < 1 := by
    intro v hv
    rw [hf]
    exact (div_lt_iff₀ hu).mpr (by simpa using hgu v (subset_closure hv))
  have hballRe : ∀ v ∈ X.closedBall 0 tau, (f v).re < 1 := by
    intro v hv
    apply hfa
    simpa only [zero_add] using Set.add_mem_add hzR hv
  have hballNorm := norm_lt_of_re_lt_on_balanced f.toLinearMap
    (X.balanced_closedBall_zero tau) hballRe
  have hdual : ∀ v, tau * ‖f v‖ ≤ X v :=
    seminorm_dual_bound_of_ball X f.toLinearMap htau
      (fun v hv => hballNorm v (X.mem_closedBall_zero.mpr hv))
  have hstructRe : ∀ Q ∈ S, (((R : ℝ) • f) Q).re < 1 := by
    intro Q hQ
    have hRQ : R • Q ∈ R • convexHull ℝ S :=
      Set.smul_mem_smul_set (subset_convexHull ℝ S hQ)
    have hQA : R • Q ∈ A := by
      simpa only [add_zero] using Set.add_mem_add hRQ hzBall
    simpa only [smul_apply, ContinuousLinearMap.map_smul_of_tower] using hfa _ hQA
  have hstruct := norm_lt_of_re_lt_on_balanced ((R : ℝ) • f).toLinearMap hS hstructRe
  refine ⟨f, hfb, hdual, ?_⟩
  intro Q hQ
  have h := hstruct Q hQ
  change ‖R • f Q‖ < 1 at h
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hR] using h

theorem mem_closure_model_set_of_dual_detector (X : Seminorm ℂ E) {S : Set E}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) {R tau : ℝ} (hR : 0 < R) (htau : 0 < tau)
    (b : E)
    (hdetect : ∀ f : E →L[ℂ] ℂ, 1 < (f b).re → (∀ v, tau * ‖f v‖ ≤ X v) →
      ∃ Q ∈ S, 1 ≤ R * ‖f Q‖) :
    b ∈ closure (R • convexHull ℝ S + X.closedBall 0 tau) := by
  by_contra hb
  obtain ⟨f, hfb, hdual, hsmall⟩ := exists_modeling_dual_obstruction X hS hSn hR htau b hb
  obtain ⟨Q, hQ, hlarge⟩ := hdetect f hfb hdual
  exact (hsmall Q hQ).not_ge hlarge

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem exists_uniform_convex_approximation {S : Set (Ω → ℂ)} {z : Ω → ℂ}
    (hz : z ∈ convexHull ℝ S) (hS : ∀ q ∈ S, ∀ x, ‖q x‖ ≤ 1)
    (n : ℕ) (hn : 0 < n) :
    ∃ q : Fin n → (Ω → ℂ), (∀ i, q i ∈ S) ∧
      (𝔼 x, ‖((n : ℝ)⁻¹ • (∑ i, q i) - z) x‖ ^ 2) ≤ 1 / (n : ℝ) := by
  let e : (Ω → ℂ) ≃ₗ[ℝ] EuclideanSpace ℂ Ω :=
    (WithLp.linearEquiv 2 ℝ (Ω → ℂ)).symm
  have hz' : e z ∈ convexHull ℝ (e '' S) := by
    change e.toLinearMap z ∈ convexHull ℝ (e.toLinearMap '' S)
    rw [← e.toLinearMap.image_convexHull S]
    exact ⟨z, hz, rfl⟩
  have hS' : ∀ v ∈ e '' S, ‖v‖ ≤ Real.sqrt (Fintype.card Ω : ℝ) := by
    rintro v ⟨q, hq, rfl⟩
    rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
      Real.sq_sqrt (Nat.cast_nonneg _)]
    change ‖(WithLp.toLp 2 q : EuclideanSpace ℂ Ω)‖ ^ 2 ≤ (Fintype.card Ω : ℝ)
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _x : Ω, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg (q x)) (hS q hq x) 2
      _ = _ := by simp
  obtain ⟨v, hv, hsq⟩ := exists_convex_empirical_average hz' hS' n hn
  let q : Fin n → (Ω → ℂ) := fun i => e.symm (v i)
  have hq : ∀ i, q i ∈ S := by
    intro i
    obtain ⟨w, hw, hew⟩ := hv i
    change e.symm (v i) ∈ S
    rw [← hew, e.symm_apply_apply]
    exact hw
  have hid : e ((n : ℝ)⁻¹ • (∑ i, q i) - z) =
      (n : ℝ)⁻¹ • (∑ i, v i) - e z := by
    simp only [map_sub, map_smul, map_sum, q, LinearEquiv.apply_symm_apply]
  rw [← hid, Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
  change ‖(WithLp.toLp 2 ((n : ℝ)⁻¹ • (∑ i, q i) - z) : EuclideanSpace ℂ Ω)‖ ^ 2 ≤
    (Fintype.card Ω : ℝ) / n at hsq
  rw [EuclideanSpace.norm_sq_eq] at hsq
  refine ⟨q, hq, ?_⟩
  rw [Fintype.expect_eq_sum_div_card]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (div_le_div_of_nonneg_right hsq (Nat.cast_nonneg _)).trans_eq
  field_simp

theorem seminorm_sq_le_square_mean (X : Seminorm ℂ (Ω → ℂ)) {K : ℝ}
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖)) (v : Ω → ℂ) :
    (X v) ^ 2 ≤ K ^ 2 * (𝔼 x, ‖v x‖ ^ 2) := by
  have h := pow_le_pow_left₀ (apply_nonneg X v) (hX v) 2
  rw [mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_left (expect_square_le (fun x => ‖v x‖)) (sq_nonneg K))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

noncomputable def weightedEuclideanMap (p : FiniteProbabilityWeights Ω) :
    (Ω → ℂ) →ₗ[ℝ] EuclideanSpace ℂ Ω :=
  (WithLp.linearEquiv 2 ℝ (Ω → ℂ)).symm.toLinearMap.comp
    (LinearMap.pi fun x => Real.sqrt (p.weight x) • LinearMap.proj x)

theorem weightedEuclideanMap_norm_sq (p : FiniteProbabilityWeights Ω) (v : Ω → ℂ) :
    ‖weightedEuclideanMap p v‖ ^ 2 = p.mean (fun x => ‖v x‖ ^ 2) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro x _
  change ‖Real.sqrt (p.weight x) • v x‖ ^ 2 = p.weight x * ‖v x‖ ^ 2
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (p.nonneg x)]

theorem exists_weighted_convex_approximation (p : FiniteProbabilityWeights Ω)
    {S : Set (Ω → ℂ)} {z : Ω → ℂ} (hz : z ∈ convexHull ℝ S)
    (hS : ∀ q ∈ S, ∀ x, ‖q x‖ ≤ 1) (n : ℕ) (hn : 0 < n) :
    ∃ q : Fin n → (Ω → ℂ), (∀ i, q i ∈ S) ∧
      p.mean (fun x => ‖((n : ℝ)⁻¹ • (∑ i, q i) - z) x‖ ^ 2) ≤ 1 / (n : ℝ) := by
  classical
  let e := weightedEuclideanMap p
  have hz' : e z ∈ convexHull ℝ (e '' S) := by
    rw [← e.image_convexHull S]
    exact ⟨z, hz, rfl⟩
  have hS' : ∀ v ∈ e '' S, ‖v‖ ≤ 1 := by
    rintro v ⟨q, hq, rfl⟩
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
    change ‖weightedEuclideanMap p q‖ ^ 2 ≤ 1 ^ 2
    rw [weightedEuclideanMap_norm_sq, one_pow]
    exact (p.mean_mono (fun x => by
      nlinarith [hS q hq x, norm_nonneg (q x)])).trans_eq (p.mean_const 1)
  obtain ⟨v, hv, hsq⟩ := exists_convex_empirical_average hz' hS' n hn
  have hpre : ∀ i, ∃ q ∈ S, e q = v i := hv
  choose q hq heq using hpre
  have hid : e ((n : ℝ)⁻¹ • (∑ i, q i) - z) =
      (n : ℝ)⁻¹ • (∑ i, v i) - e z := by
    simp only [map_sub, map_smul, map_sum, heq]
  rw [← hid, one_pow] at hsq
  exact ⟨q, hq, (weightedEuclideanMap_norm_sq p _).ge.trans hsq⟩

theorem seminorm_sq_le_weighted_square_mean (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {K : ℝ}
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖)) (v : Ω → ℂ) :
    (X v) ^ 2 ≤ K ^ 2 * p.mean (fun x => ‖v x‖ ^ 2) := by
  have h := pow_le_pow_left₀ (apply_nonneg X v) (hX v) 2
  rw [mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (p.mean_square_le (fun x => ‖v x‖)) (sq_nonneg K))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

omit [DecidableEq Ω] [Nonempty Ω] in
theorem norm_uniform_inner_symm (v w : Ω → ℂ) :
    ‖𝔼 x, v x * star (w x)‖ = ‖𝔼 x, w x * star (v x)‖ := by
  have h : star (𝔼 x, v x * star (w x)) = 𝔼 x, w x * star (v x) := by
    simp [Fintype.expect_eq_sum_div_card, mul_comm]
  rw [← h, norm_star]

theorem mem_closure_model_of_uniform_detector
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)} (hS : Balanced ℂ S) (hSn : S.Nonempty)
    {K M beta tau : ℝ} (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖𝔼 x, psi x * star (Q x)‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    b ∈ closure ((2 / beta : ℝ) • convexHull ℝ S + X.closedBall 0 tau) := by
  apply mem_closure_model_set_of_dual_detector X hS hSn (by positivity) htau b
  intro f hfb hdual
  have hcap := uniformDualVector_cap X f.toLinearMap htau hX hdual
  have hlarge := uniformDualVector_detectable X f.toLinearMap b hM htau hb hfb hdual
  obtain ⟨Q, hQ, hcor⟩ := hdetect (uniformDualVector f.toLinearMap) hcap hlarge.le
  rw [norm_uniform_inner_symm, ← functional_eq_uniform_inner] at hcor
  refine ⟨Q, hQ, ?_⟩
  have h := mul_le_mul_of_nonneg_left hcor (show 0 ≤ 2 / beta by positivity)
  rw [div_mul_cancel₀ 2 hbeta.ne'] at h
  exact (by norm_num : (1 : ℝ) ≤ 2).trans h

theorem exists_convex_model_of_uniform_detector
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)} (hS : Balanced ℂ S) (hSn : S.Nonempty)
    {K M beta tau eta : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta)
    (htau : 0 < tau) (heta : 0 < eta)
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖𝔼 x, psi x * star (Q x)‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ z ∈ convexHull ℝ S, X (b - (2 / beta : ℝ) • z) ≤ tau + eta := by
  have hc := mem_closure_model_of_uniform_detector X hS hSn hM hbeta htau hX hdetect b hb
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hc (eta / (K + 1)) (by positivity)
  obtain ⟨v, hv, e, he, hve⟩ := Set.mem_add.mp hy
  obtain ⟨z, hz, hzv⟩ := Set.mem_smul_set.mp hv
  have hxe : X e ≤ tau := X.mem_closedBall_zero.mp he
  have hnorm : ‖b - y‖ < eta / (K + 1) := by
    simpa only [dist_eq_norm] using hdist
  have hsmall : K * ‖b - y‖ ≤ eta := by
    have h := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp hnorm
    nlinarith [norm_nonneg (b - y)]
  have hmean : (𝔼 x, ‖(b - y) x‖) ≤ ‖b - y‖ :=
    (Finset.expect_le_expect (fun x (_ : x ∈ Finset.univ) => norm_le_pi_norm (b - y) x)).trans_eq
      (Finset.expect_const Finset.univ_nonempty ‖b - y‖)
  have hxy : X (b - y) ≤ eta := (hX (b - y)).trans
    ((mul_le_mul_of_nonneg_left hmean hK).trans hsmall)
  refine ⟨z, hz, ?_⟩
  have hid : b - (2 / beta : ℝ) • z = (b - y) + e := by
    rw [← hve, ← hzv]
    abel
  rw [hid]
  exact (map_add_le_add X _ _).trans (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_empirical_length {R K tau : ℝ} (htau : 0 < tau) :
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ 1 + R ^ 2 * K ^ 2 / tau ^ 2 ∧
      Real.sqrt (R ^ 2 * K ^ 2 / n) < tau := by
  let t := R ^ 2 * K ^ 2 / tau ^ 2
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  let n := ⌊t⌋₊ + 1
  have hn : 0 < n := by dsimp only [n]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlen : (n : ℝ) ≤ 1 + t := by
    dsimp only [n]
    push_cast
    linarith [Nat.floor_le ht]
  have hlt : t < (n : ℝ) := by
    simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  have hprod : R ^ 2 * K ^ 2 < tau ^ 2 * n := by
    have h := (div_lt_iff₀ (pow_pos htau 2)).mp hlt
    simpa only [mul_comm] using h
  have hsmall : R ^ 2 * K ^ 2 / n < tau ^ 2 := (div_lt_iff₀ hnR).mpr hprod
  have hsquare := Real.sq_sqrt (show 0 ≤ R ^ 2 * K ^ 2 / n by positivity)
  refine ⟨n, hn, hlen, ?_⟩
  nlinarith [Real.sqrt_nonneg (R ^ 2 * K ^ 2 / n)]

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

theorem scaled_empirical_seminorm_bound (X : Seminorm ℂ (Ω → ℂ)) {K R : ℝ}
    (hR : 0 ≤ R) (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (v : Ω → ℂ) (n : ℕ) (hn : 0 < n) (hv : (𝔼 x, ‖v x‖ ^ 2) ≤ 1 / (n : ℝ)) :
    X (R • v) ≤ Real.sqrt (R ^ 2 * K ^ 2 / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := (seminorm_sq_le_square_mean X hX v).trans
    (mul_le_mul_of_nonneg_left hv (sq_nonneg K))
  have hsmul : X (R • v) = R * X v := by
    change (X.restrictScalars ℝ) (R • v) = _
    rw [map_smul_eq_mul, Real.norm_of_nonneg hR]
    rfl
  have hscaled : (X (R • v)) ^ 2 ≤ R ^ 2 * K ^ 2 / n := by
    rw [hsmul, mul_pow]
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg R)
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_assoc] using h
  have hroot := Real.sq_sqrt (show 0 ≤ R ^ 2 * K ^ 2 / n by positivity)
  exact (sq_le_sq₀ (apply_nonneg X _) (Real.sqrt_nonneg _)).mp (hscaled.trans_eq hroot.symm)

variable [DecidableEq Ω]

theorem exists_uniform_model_of_detector
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {K M beta tau : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * (𝔼 x, ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖𝔼 x, psi x * star (Q x)‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧ X e ≤ 2 * tau ∧
      (n : ℝ) ≤ 1 + 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let R := 2 / beta
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨n, hn, hlen, hsmall⟩ := exists_empirical_length (R := R) (K := K) htau
  let s := Real.sqrt (R ^ 2 * K ^ 2 / n)
  have hs : s < tau := hsmall
  let eta := (tau - s) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  obtain ⟨z, hz, hmodel⟩ := exists_convex_model_of_uniform_detector X hS hSn hK hM hbeta htau
    heta hX hdetect b hb
  obtain ⟨Q, hQ, happrox⟩ := exists_uniform_convex_approximation hz hSbound n hn
  let avg := (n : ℝ)⁻¹ • (∑ i, Q i)
  have hnoise : X (R • (avg - z)) ≤ s :=
    scaled_empirical_seminorm_bound X hR.le hX (avg - z) n hn happrox
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let c : Fin n → ℝ := fun _ => R / n
  have hstruct : (∑ i, c i • Q i) = R • avg := by
    calc
      _ = (R / (n : ℝ)) • (∑ i, Q i) := by rw [Finset.smul_sum]
      _ = _ := by dsimp only [avg]; rw [smul_smul]; congr 1
  have hcost : (∑ i, |c i|) = R := by
    simp only [c, abs_of_nonneg (div_nonneg hR.le hnR.le), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨n, hn, Q, c, b - ∑ i, c i • Q i, hQ, ?_, hcost.le, ?_, ?_⟩
  · abel
  · rw [hstruct]
    have hid : b - R • avg = (b - R • z) - R • (avg - z) := by
      rw [smul_sub]
      abel
    rw [hid]
    have h := map_sub_le_add X (b - R • z) (R • (avg - z))
    change X (b - R • z) ≤ tau + eta at hmodel
    dsimp only [eta] at hmodel
    linarith
  · have heq : R ^ 2 * K ^ 2 / tau ^ 2 = 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
      dsimp only [R]
      field_simp
      ring
    simpa only [heq] using hlen

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem mem_closure_model_of_weighted_detector (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)} (hS : Balanced ℂ S) (hSn : S.Nonempty)
    {K M beta tau : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    b ∈ closure ((2 / beta : ℝ) • convexHull ℝ S + X.closedBall 0 tau) := by
  apply mem_closure_model_set_of_dual_detector X hS hSn (by positivity) htau b
  intro f hfb hdual
  have hzero := modeling_dual_zero_weight p X f.toLinearMap htau hX hdual
  have hcap := weightedDualVector_cap p X f.toLinearMap hK htau hX hdual
  have hlarge := weightedDualVector_detectable p X f.toLinearMap b hM htau hb hfb hdual hzero
  obtain ⟨Q, hQ, hcor⟩ := hdetect (weightedDualVector p f.toLinearMap) hcap hlarge.le
  rw [p.norm_correlation_symm, ← functional_eq_weighted_inner p f.toLinearMap hzero] at hcor
  refine ⟨Q, hQ, ?_⟩
  have h := mul_le_mul_of_nonneg_left hcor (show 0 ≤ 2 / beta by positivity)
  rw [div_mul_cancel₀ 2 hbeta.ne'] at h
  exact (by norm_num : (1 : ℝ) ≤ 2).trans h

theorem exists_convex_model_of_weighted_detector (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)} (hS : Balanced ℂ S) (hSn : S.Nonempty)
    {K M beta tau eta : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta)
    (htau : 0 < tau) (heta : 0 < eta)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ z ∈ convexHull ℝ S, X (b - (2 / beta : ℝ) • z) ≤ tau + eta := by
  have hc := mem_closure_model_of_weighted_detector p X hS hSn hK hM hbeta htau hX hdetect b hb
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp hc (eta / (K + 1)) (by positivity)
  obtain ⟨v, hv, e, he, hve⟩ := Set.mem_add.mp hy
  obtain ⟨z, hz, hzv⟩ := Set.mem_smul_set.mp hv
  have hxe : X e ≤ tau := X.mem_closedBall_zero.mp he
  have hnorm : ‖b - y‖ < eta / (K + 1) := by
    simpa only [dist_eq_norm] using hdist
  have hsmall : K * ‖b - y‖ ≤ eta := by
    have h := (lt_div_iff₀ (show 0 < K + 1 by linarith)).mp hnorm
    nlinarith [norm_nonneg (b - y)]
  have hmean : p.mean (fun x => ‖(b - y) x‖) ≤ ‖b - y‖ :=
    (p.mean_mono (fun x => norm_le_pi_norm (b - y) x)).trans_eq (p.mean_const ‖b - y‖)
  have hxy : X (b - y) ≤ eta := (hX (b - y)).trans
    ((mul_le_mul_of_nonneg_left hmean hK).trans hsmall)
  refine ⟨z, hz, ?_⟩
  have hid : b - (2 / beta : ℝ) • z = (b - y) + e := by
    rw [← hve, ← hzv]
    abel
  rw [hid]
  exact (map_add_le_add X _ _).trans (by linarith)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem scaled_weighted_empirical_seminorm_bound (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {K R : ℝ} (hR : 0 ≤ R)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (v : Ω → ℂ) (n : ℕ) (hn : 0 < n)
    (hv : p.mean (fun x => ‖v x‖ ^ 2) ≤ 1 / (n : ℝ)) :
    X (R • v) ≤ Real.sqrt (R ^ 2 * K ^ 2 / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq := (seminorm_sq_le_weighted_square_mean p X hX v).trans
    (mul_le_mul_of_nonneg_left hv (sq_nonneg K))
  have hsmul : X (R • v) = R * X v := by
    change (X.restrictScalars ℝ) (R • v) = _
    rw [map_smul_eq_mul, Real.norm_of_nonneg hR]
    rfl
  have hscaled : (X (R • v)) ^ 2 ≤ R ^ 2 * K ^ 2 / n := by
    rw [hsmul, mul_pow]
    have h := mul_le_mul_of_nonneg_left hsq (sq_nonneg R)
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_assoc] using h
  have hroot := Real.sq_sqrt (show 0 ≤ R ^ 2 * K ^ 2 / n by positivity)
  exact (sq_le_sq₀ (apply_nonneg X _) (Real.sqrt_nonneg _)).mp (hscaled.trans_eq hroot.symm)

variable [DecidableEq Ω]

theorem exists_weighted_model_of_detector (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {K M beta tau : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧ X e ≤ 2 * tau ∧
      (n : ℝ) ≤ 1 + 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let R := 2 / beta
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨n, hn, hlen, hsmall⟩ := exists_empirical_length (R := R) (K := K) htau
  let s := Real.sqrt (R ^ 2 * K ^ 2 / n)
  have hs : s < tau := hsmall
  let eta := (tau - s) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  obtain ⟨z, hz, hmodel⟩ := exists_convex_model_of_weighted_detector p X hS hSn
    hK hM hbeta htau heta hX hdetect b hb
  obtain ⟨Q, hQ, happrox⟩ := exists_weighted_convex_approximation p hz hSbound n hn
  let avg := (n : ℝ)⁻¹ • (∑ i, Q i)
  have hnoise : X (R • (avg - z)) ≤ s :=
    scaled_weighted_empirical_seminorm_bound p X hR.le hX (avg - z) n hn happrox
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let c : Fin n → ℝ := fun _ => R / n
  have hstruct : (∑ i, c i • Q i) = R • avg := by
    calc
      _ = (R / (n : ℝ)) • (∑ i, Q i) := by rw [Finset.smul_sum]
      _ = _ := by dsimp only [avg]; rw [smul_smul]; congr 1
  have hcost : (∑ i, |c i|) = R := by
    simp only [c, abs_of_nonneg (div_nonneg hR.le hnR.le), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  refine ⟨n, hn, Q, c, b - ∑ i, c i • Q i, hQ, ?_, hcost.le, ?_, ?_⟩
  · abel
  · rw [hstruct]
    have hid : b - R • avg = (b - R • z) - R • (avg - z) := by
      rw [smul_sub]
      abel
    rw [hid]
    have h := map_sub_le_add X (b - R • z) (R • (avg - z))
    change X (b - R • z) ≤ tau + eta at hmodel
    dsimp only [eta] at hmodel
    linarith
  · have heq : R ^ 2 * K ^ 2 / tau ^ 2 = 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
      dsimp only [R]
      field_simp
      ring
    simpa only [heq] using hlen

theorem exists_finite_probability_model (p : FiniteProbabilityWeights Ω)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {K M beta tau : ℝ} (hK : 0 ≤ K) (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * p.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K / tau) → tau / M ^ 2 ≤ X psi →
      ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℂ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, ‖c i‖) ≤ 2 / beta ∧ X e ≤ 2 * tau ∧
      (n : ℝ) ≤ 1 + 4 * K ^ 2 / (beta ^ 2 * tau ^ 2) := by
  obtain ⟨n, hn, Q, c, e, hQ, hb', hc, he, hlen⟩ :=
    exists_weighted_model_of_detector p X hS hSn hSbound hK hM hbeta htau hX hdetect b hb
  refine ⟨n, hn, Q, fun i => (c i : ℂ), e, hQ, ?_, ?_, he, hlen⟩
  · have hreal (i) : (c i : ℂ) • Q i = c i • Q i := by
      ext x
      exact Complex.real_smul.symm
    simpa only [hreal] using hb'
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using hc

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem seminorm_mask_le (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C C₀ : ℝ}
    (hC : 0 ≤ C) (_hC₀ : 0 ≤ C₀)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (hgood : ∀ x ∈ G, m x ≤ C₀) (v : Ω → ℂ) :
    X (finiteMask G v) ≤ C * C₀ * p.mean (fun x => if x ∈ G then ‖v x‖ else 0) := by
  have hmean : p.mean (fun x => m x * ‖finiteMask G v x‖) ≤
      C₀ * p.mean (fun x => if x ∈ G then ‖v x‖ else 0) := by
    rw [← p.mean_const_mul]
    apply p.mean_mono
    intro x
    by_cases hx : x ∈ G
    · simpa only [finiteMask_apply, hx, ite_true] using
        mul_le_mul_of_nonneg_right (hgood x hx) (norm_nonneg (v x))
    · simp [hx]
  exact (hX _).trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hmean hC)

theorem seminorm_mask_le_condition (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (hG : 0 < p.mass G) (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C C₀ : ℝ}
    (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (hgood : ∀ x ∈ G, m x ≤ C₀) (v : Ω → ℂ) :
    X (finiteMask G v) ≤ C * C₀ * (p.condition G hG).mean (fun x => ‖v x‖) := by
  have h := seminorm_mask_le p G X m hC hC₀ hX hgood v
  rw [← p.mass_mul_condition_mean G hG] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hC₀)
  exact mul_le_of_le_one_left ((p.condition G hG).mean_nonneg (fun x => norm_nonneg _))
    (p.mass_le_one G)

theorem seminorm_tail_le (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C B : ℝ}
    (hC : 0 ≤ C) (hm : ∀ x, 0 ≤ m x)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (v : Ω → ℂ) (hv : ∀ x, ‖v x‖ ≤ B) :
    X (v - finiteMask G v) ≤ C * B * p.mean (fun x => if x ∈ G then 0 else m x) := by
  have hmean : p.mean (fun x => m x * ‖(v - finiteMask G v) x‖) ≤
      B * p.mean (fun x => if x ∈ G then 0 else m x) := by
    rw [← p.mean_const_mul]
    apply p.mean_mono
    intro x
    by_cases hx : x ∈ G
    · simp [hx]
    · simpa only [Pi.sub_apply, finiteMask_apply, hx, ite_false, sub_zero, mul_comm B]
        using mul_le_mul_of_nonneg_left (hv x) (hm x)
  exact (hX _).trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hmean hC)

theorem seminorm_le_mask_add_tail (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {C B : ℝ}
    (hC : 0 ≤ C) (hm : ∀ x, 0 ≤ m x)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (v : Ω → ℂ) (hv : ∀ x, ‖v x‖ ≤ B) :
    X v ≤ X (finiteMask G v) +
      C * B * p.mean (fun x => if x ∈ G then 0 else m x) := by
  calc
    X v = X (finiteMask G v + (v - finiteMask G v)) := by congr 1; abel
    _ ≤ X (finiteMask G v) + X (v - finiteMask G v) := map_add_le_add X _ _
    _ ≤ _ := add_le_add le_rfl (seminorm_tail_le p G X m hC hm hX v hv)

omit [Fintype Ω] [DecidableEq Ω] in

theorem model_error_norm_le {ι : Type*} [Fintype ι]
    {b e : Ω → ℂ} {Q : ι → (Ω → ℂ)} {c : ι → ℝ} {M R : ℝ}
    (hb : ∀ x, ‖b x‖ ≤ M) (hQ : ∀ i x, ‖Q i x‖ ≤ 1)
    (hdecomp : b = (∑ i, c i • Q i) + e) (hc : (∑ i, |c i|) ≤ R) :
    ∀ x, ‖e x‖ ≤ M + R := by
  intro x
  have hsum : ‖(∑ i, c i • Q i) x‖ ≤ R := by
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i _ => ?_)).trans hc
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hQ i x)
  have he : e x = b x - (∑ i, c i • Q i) x := by
    have h := congrFun hdecomp x
    simp only [Pi.add_apply] at h
    exact eq_sub_of_add_eq' h.symm
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (hb x) hsum)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem exists_model_with_tail_error (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {C C₀ M beta tau : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hm : ∀ x, 0 ≤ m x) (hgood : ∀ x ∈ G, m x ≤ C₀)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ C * C₀ / tau) →
      tau / M ^ 2 ≤ X psi → ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      X e ≤ 2 * tau + C * (M + 2 / beta) *
        p.mean (fun x => if x ∈ G then 0 else m x) ∧
      (n : ℝ) ≤ 1 + 4 * (C * C₀) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  have hK : 0 ≤ C * C₀ := mul_nonneg hC hC₀
  have hR : 0 ≤ 2 / beta := by positivity
  have htail : 0 ≤ p.mean (fun x => if x ∈ G then 0 else m x) :=
    p.mean_nonneg (fun x => by split_ifs; exact le_rfl; exact hm x)
  by_cases hG : 0 < p.mass G
  · let XG := X.comp (finiteMask G)
    have hXG (v : Ω → ℂ) : XG v ≤
        (C * C₀) * (p.condition G hG).mean (fun x => ‖v x‖) :=
      seminorm_mask_le_condition p G hG X m hC hC₀ hX hgood v
    have hdetG (psi : Ω → ℂ) (hpsi : ∀ x, ‖psi x‖ ≤ C * C₀ / tau)
        (hlarge : tau / M ^ 2 ≤ XG psi) :
        ∃ Q ∈ S, beta ≤ ‖(p.condition G hG).correlation psi Q‖ := by
      have hmask : ∀ x, ‖finiteMask G psi x‖ ≤ C * C₀ / tau := by
        intro x
        by_cases hx : x ∈ G
        · simpa [hx] using hpsi x
        · simpa [hx] using div_nonneg hK htau.le
      obtain ⟨Q, hQ, hcorr⟩ := hdetect (finiteMask G psi) hmask hlarge
      refine ⟨Q, hQ, hcorr.trans ?_⟩
      rw [p.norm_correlation_mask G hG]
      exact mul_le_of_le_one_left (norm_nonneg _) (p.mass_le_one G)
    obtain ⟨n, hn, Q, c, e, hQ, hdecomp, hc, he, hlen⟩ :=
      exists_weighted_model_of_detector (p.condition G hG) XG hS hSn hSbound
        hK hM hbeta htau hXG hdetG b hb
    refine ⟨n, hn, Q, c, e, hQ, hdecomp, hc, ?_, hlen⟩
    have herror := model_error_norm_le hb (fun i => hSbound (Q i) (hQ i)) hdecomp hc
    have hglobal := seminorm_le_mask_add_tail p G X m hC hm hX e herror
    exact hglobal.trans (add_le_add he le_rfl)
  · have hmass : p.mass G = 0 := le_antisymm (le_of_not_gt hG) (p.mass_nonneg G)
    obtain ⟨Q₀, hQ₀⟩ := hSn
    refine ⟨1, by decide, fun _ => Q₀, fun _ => 0, b, fun _ => hQ₀, ?_, ?_, ?_, ?_⟩
    · simp
    · simpa using hR
    · have hmask : X (finiteMask G b) ≤ 0 := by
        have h := seminorm_mask_le p G X m hC hC₀ hX hgood b
        simpa [p.mean_mask_zero G hmass] using h
      have hglobal := seminorm_le_mask_add_tail p G X m hC hm hX b hb
      have hmono : C * M * p.mean (fun x => if x ∈ G then 0 else m x) ≤
          C * (M + 2 / beta) * p.mean (fun x => if x ∈ G then 0 else m x) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hR) hC) htail
      linarith
    · have hnonneg : 0 ≤ 4 * (C * C₀) ^ 2 / (beta ^ 2 * tau ^ 2) := by positivity
      simpa using (le_add_of_nonneg_right hnonneg : (1 : ℝ) ≤ 1 + _)

theorem exists_model_of_small_weighted_tail
    (p : FiniteProbabilityWeights Ω) (G : Finset Ω)
    (X : Seminorm ℂ (Ω → ℂ)) (m : Ω → ℝ) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {C C₀ M beta tau eta : ℝ} (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀)
    (hM : 0 < M) (hbeta : 0 < beta) (htau : 0 < tau)
    (hm : ∀ x, 0 ≤ m x) (hgood : ∀ x ∈ G, m x ≤ C₀)
    (hX : ∀ v, X v ≤ C * p.mean (fun x => m x * ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ C * C₀ / tau) →
      tau / M ^ 2 ≤ X psi → ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (htail : C * (M + 2 / beta) * p.mean (fun x => if x ∈ G then 0 else m x) ≤
      eta - 2 * tau)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ M) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧ X e ≤ eta ∧
      (n : ℝ) ≤ 1 + 4 * (C * C₀) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  obtain ⟨n, hn, Q, c, e, hQ, hdecomp, hc, he, hlen⟩ :=
    exists_model_with_tail_error p G X m hS hSn hSbound hC hC₀ hM hbeta htau
      hm hgood hX hdetect b hb
  exact ⟨n, hn, Q, c, e, hQ, hdecomp, hc, by linarith, hlen⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem exists_model_of_marginal_excess {Ω : Type*} [Fintype Ω]
    (p q : FiniteProbabilityWeights Ω) (hp : ∀ x, 0 < p.weight x)
    (X : Seminorm ℂ (Ω → ℂ)) {S : Set (Ω → ℂ)}
    (hS : Balanced ℂ S) (hSn : S.Nonempty) (hSbound : ∀ Q ∈ S, ∀ x, ‖Q x‖ ≤ 1)
    {K C B beta tau ε : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hB : 0 < B) (hbeta : 0 < beta) (htau : 0 < tau)
    (hX : ∀ v, X v ≤ K * q.mean (fun x => ‖v x‖))
    (hdetect : ∀ psi : Ω → ℂ, (∀ x, ‖psi x‖ ≤ K * (2*C) / tau) →
      tau / B ^ 2 ≤ X psi → ∃ Q ∈ S, beta ≤ ‖p.correlation psi Q‖)
    (hexcess : p.excessMass q C ≤ ε)
    (b : Ω → ℂ) (hb : ∀ x, ‖b x‖ ≤ B) :
    ∃ (n : ℕ) (_ : 0 < n) (Q : Fin n → (Ω → ℂ)) (c : Fin n → ℝ) (e : Ω → ℂ),
      (∀ i, Q i ∈ S) ∧ b = (∑ i, c i • Q i) + e ∧
      (∑ i, |c i|) ≤ 2 / beta ∧
      X e ≤ 2*tau + 2*K*(B + 2/beta)*ε ∧
      (n : ℝ) ≤ 1 + 4 * (K * (2*C)) ^ 2 / (beta ^ 2 * tau ^ 2) := by
  let G := Finset.univ.filter (fun x => p.relativeDensity q x ≤ 2*C)
  have htail : p.mean (fun x => if x ∈ G then 0 else p.relativeDensity q x) ≤ 2*ε := by
    rw [p.relativeDensity_tail_mass q hp]
    exact FiniteProbabilityWeights.mass_above_double_cap_le_of_excess p q hexcess
  have hbound (v : Ω → ℂ) : X v ≤ K * p.mean (fun x => p.relativeDensity q x * ‖v x‖) := by
    rw [p.mean_relativeDensity q hp]
    exact hX v
  obtain ⟨n, hn, Q, c, e, hQ, hdecomp, hc, he, hlen⟩ :=
    exists_model_with_tail_error p G X (p.relativeDensity q) hS hSn hSbound hK
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) hB hbeta htau
      (p.relativeDensity_nonneg q) (fun x hx => (Finset.mem_filter.mp hx).2)
      hbound hdetect b hb
  refine ⟨n, hn, Q, c, e, hQ, hdecomp, hc, ?_, hlen⟩
  have hscale : 0 ≤ K*(B + 2/beta) := by positivity
  have hsmall := mul_le_mul_of_nonneg_left htail hscale
  nlinarith

end Erdos3

end

end OAI
