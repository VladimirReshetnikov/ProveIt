import IntegerPoints.Lemma1
import IntegerPoints.FouvryIwaniec
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Tools for Zhai–Cao, Lemma 9

Two consequences of Lemmas 1 and 6 in the shape needed by Heath-Brown's
method:

* `L9.inner_sum_bound`: for `λ ≠ 0`,
  `‖∑_{u ∼ U} e(√x λ / u)‖ ≤ C (U²/(√x|λ|) + x^{1/4} |λ|^{1/2} U^{-1/2})`
  (Lemma 1 with `f(u) = √x λ/u`, `|f'| ≍ √x|λ|/U²`, `|f''| ≍ |f'|/U`; `f` is
  extended smoothly below `1/2` so that Lemma 1's global `C²` hypothesis holds).
* `L9.count_close`: the number of pairs `((v₁, n₁), (v₂, n₂))`, `v ∼ V`, `n ∼ N`,
  with `|√n₁/v₁ − √n₂/v₂| ≤ t` is at most
  `C₆ (NV log(2NV) + (4tV/√N) N² V²)` (Lemma 6 with `α = 1/2`, `β = 1`).
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace L9

/-! ### A smooth positive function equal to `u` on `[1/2, ∞)` -/

/-- `hfun u = u` for `u ≥ 1/2`, `hfun > 0` everywhere, smooth. -/
noncomputable def hfun (u : ℝ) : ℝ :=
  Real.smoothTransition (4 * u - 1) * u + (1 - Real.smoothTransition (4 * u - 1)) * (1 / 2)

theorem hfun_eq {u : ℝ} (hu : 1 / 2 ≤ u) : hfun u = u := by
  unfold hfun
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem hfun_pos (u : ℝ) : 0 < hfun u := by
  unfold hfun
  rcases le_or_gt u (1 / 4) with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num
  · have h0 := Real.smoothTransition.nonneg (4 * u - 1)
    have h1 := Real.smoothTransition.le_one (4 * u - 1)
    nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ u - 1 / 4)]

theorem hfun_contDiff : ContDiff ℝ 2 hfun := by
  have hg : ContDiff ℝ 2 (fun u : ℝ => 4 * u - 1) :=
    (contDiff_const.mul contDiff_id).sub contDiff_const
  have hτ : ContDiff ℝ 2 (fun u : ℝ => Real.smoothTransition (4 * u - 1)) :=
    (Real.smoothTransition.contDiff (n := 2)).comp hg
  exact (hτ.mul contDiff_id).add ((contDiff_const.sub hτ).mul contDiff_const)

/-- The test function `u ↦ c / hfun u`, equal to `c/u` on `[1/2, ∞)`. -/
noncomputable def ftest (c u : ℝ) : ℝ := c / hfun u

theorem ftest_contDiff (c : ℝ) : ContDiff ℝ 2 (ftest c) :=
  contDiff_const.div hfun_contDiff fun u => (hfun_pos u).ne'

theorem ftest_eventuallyEq {c u : ℝ} (hu : 1 / 2 < u) :
    ftest c =ᶠ[nhds u] fun v => c / v := by
  filter_upwards [Ioi_mem_nhds hu] with v hv
  simp only [ftest, hfun_eq (le_of_lt hv)]

theorem hasDerivAt_cdiv {c u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun v : ℝ => c / v) (-c / u ^ 2) u := by
  have h : (fun v : ℝ => c / v) = fun v => c * v⁻¹ := by
    funext v
    rw [div_eq_mul_inv]
  rw [h]
  exact ((hasDerivAt_inv hu).const_mul c).congr_deriv (by ring)

theorem deriv_cdiv_eventuallyEq {c u : ℝ} (hu : 0 < u) :
    deriv (fun v : ℝ => c / v) =ᶠ[nhds u] fun v => -c / v ^ 2 := by
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact (hasDerivAt_cdiv (ne_of_gt hv)).deriv

theorem hasDerivAt_cdiv2 {c u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun v : ℝ => -c / v ^ 2) (2 * c / u ^ 3) u := by
  have h : (fun v : ℝ => -c / v ^ 2) = fun v => -c * (v ^ 2)⁻¹ := by
    funext v
    rw [div_eq_mul_inv]
  rw [h]
  refine (((hasDerivAt_pow 2 u).inv (pow_ne_zero 2 hu)).const_mul (-c)).congr_deriv ?_
  field_simp
  ring

theorem deriv_ftest {c u : ℝ} (hu : 1 / 2 < u) : deriv (ftest c) u = -c / u ^ 2 := by
  rw [(ftest_eventuallyEq hu).deriv_eq]
  exact (hasDerivAt_cdiv (by linarith)).deriv

theorem iteratedDeriv_two_ftest {c u : ℝ} (hu : 1 / 2 < u) :
    iteratedDeriv 2 (ftest c) u = 2 * c / u ^ 3 := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, (ftest_eventuallyEq hu).deriv.deriv_eq,
    (deriv_cdiv_eventuallyEq (by linarith)).deriv_eq]
  exact (hasDerivAt_cdiv2 (by linarith)).deriv

/-! ### The inner sum `∑_{u ∼ U} e(√x λ/u)` -/

/-- Lemma 1 for `f(u) = √x λ/u`. -/
theorem inner_sum_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x U lam : ℝ), 1 ≤ U → 0 < x → lam ≠ 0 →
    ‖∑ u ∈ dyadic U, e (Real.sqrt x * lam / u)‖ ≤
      C * (U ^ 2 / (Real.sqrt x * |lam|) +
        x ^ ((1 : ℝ) / 4) * |lam| ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨C, hC⟩ := zhaiCao_lemma1_holds 2 (1 / 4) 1 (1 / 4) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max C 0, le_max_right _ _, fun x U lam hU hx hlam => ?_⟩
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hl : 0 < |lam| := abs_pos.2 hlam
  set c : ℝ := Real.sqrt x * lam with hc
  set lam' : ℝ := Real.sqrt x * |lam| / U ^ 2 with hlam'
  have hlam'0 : 0 < lam' := by positivity
  have hU0 : 0 < U := by linarith
  have hcabs : |c| = Real.sqrt x * |lam| := by rw [hc, abs_mul, abs_of_pos hsx]
  -- the derivative bounds on `[U, 2U]`
  have hd1 : ∀ t ∈ Set.Icc U (2 * U), 1 / 4 * lam' ≤ |deriv (ftest c) t| ∧
      |deriv (ftest c) t| ≤ 1 * lam' := by
    intro t ht
    have ht0 : 1 / 2 < t := by linarith [ht.1]
    rw [deriv_ftest ht0, abs_div, abs_neg, hcabs, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2),
      hlam']
    have h1 : U ^ 2 ≤ t ^ 2 := by nlinarith [ht.1]
    have h2 : t ^ 2 ≤ 4 * U ^ 2 := by nlinarith [ht.2]
    have hnum : 0 ≤ Real.sqrt x * |lam| := by positivity
    constructor
    · rw [show 1 / 4 * (Real.sqrt x * |lam| / U ^ 2) = Real.sqrt x * |lam| / (4 * U ^ 2) by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · rw [one_mul]
      exact div_le_div_of_nonneg_left hnum (by positivity) h1
  have hd2 : ∀ t ∈ Set.Icc U (2 * U), 1 / 4 * lam' / U ≤ |iteratedDeriv 2 (ftest c) t| ∧
      |iteratedDeriv 2 (ftest c) t| ≤ 2 * lam' / U := by
    intro t ht
    have ht0 : 1 / 2 < t := by linarith [ht.1]
    rw [iteratedDeriv_two_ftest ht0, abs_div, abs_mul, abs_two, hcabs,
      abs_of_pos (by positivity : (0 : ℝ) < t ^ 3), hlam']
    have h1 : U ^ 3 ≤ t ^ 3 := by
      have := ht.1
      exact pow_le_pow_left₀ hU0.le this 3
    have h2 : t ^ 3 ≤ 8 * U ^ 3 := by
      have := pow_le_pow_left₀ (by linarith [ht.1]) ht.2 3
      linarith
    have hnum : 0 ≤ Real.sqrt x * |lam| := by positivity
    constructor
    · rw [show 1 / 4 * (Real.sqrt x * |lam| / U ^ 2) / U = Real.sqrt x * |lam| / (4 * U ^ 3) by
          ring, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    · rw [show 2 * (Real.sqrt x * |lam| / U ^ 2) / U = 2 * (Real.sqrt x * |lam|) / U ^ 3 by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hmain := hC U lam' (ftest c) hU hlam'0 (ftest_contDiff c) hd1 hd2
  -- the sum is over `dyadic U` and `ftest c = c / u` there
  have hsum : ∑ n ∈ intRange U (2 * U), e (ftest c n) = ∑ u ∈ dyadic U, e (Real.sqrt x * lam / u) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ n := by
      simp only [dyadic, intRange, Finset.mem_Ioc] at hn
      have : 1 ≤ n := by omega
      exact_mod_cast this
    rw [ftest, hfun_eq (by linarith), hc]
  rw [hsum] at hmain
  -- rewrite the bound
  have hU2 : (U ^ 2) ^ ((1 : ℝ) / 2) = U := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU0.le]
    norm_num
  have hx4 : (Real.sqrt x) ^ ((1 : ℝ) / 2) = x ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
    norm_num
  have hUm : U ^ (-(1 : ℝ) / 2) = U ^ ((1 : ℝ) / 2) / U := by
    rw [← Real.rpow_sub_one hU0.ne']
    norm_num
  have hbound : lam'⁻¹ + lam' ^ ((1 : ℝ) / 2) * U ^ ((1 : ℝ) / 2) =
      U ^ 2 / (Real.sqrt x * |lam|) +
        x ^ ((1 : ℝ) / 4) * |lam| ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2) := by
    rw [hlam', inv_div, Real.div_rpow (by positivity) (by positivity),
      Real.mul_rpow hsx.le hl.le, hU2, hx4, hUm]
    ring
  rw [hbound] at hmain
  have hX : 0 ≤ U ^ 2 / (Real.sqrt x * |lam|) +
      x ^ ((1 : ℝ) / 4) * |lam| ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2) := by positivity
  exact hmain.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hX)

/-! ### Counting close pairs via Lemma 6 -/

/-- `λ((v₁, n₁), (v₂, n₂)) = √n₁/v₁ − √n₂/v₂`. -/
noncomputable def lamOf (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  Real.sqrt p.1.2 / p.1.1 - Real.sqrt p.2.2 / p.2.1

/-- The pairs `((v₁, n₁), (v₂, n₂))` with `v ∼ V`, `n ∼ N`. -/
noncomputable def pairSet (V N : ℝ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (dyadic V ×ˢ dyadic N) ×ˢ (dyadic V ×ˢ dyadic N)

theorem dyadic_subset_closedRange {M : ℝ} (hM : 0 ≤ M) : dyadic M ⊆ closedRange M (2 * M) := by
  intro n hn
  rw [dyadic, intRange, Finset.mem_Ioc] at hn
  rw [closedRange, Finset.mem_Icc]
  refine ⟨?_, hn.2⟩
  have := Nat.ceil_le_floor_add_one M
  omega

theorem mem_dyadic_bounds {M : ℝ} (hM : 0 ≤ M) {n : ℕ} (hn : n ∈ dyadic M) :
    M < n ∧ (n : ℝ) ≤ 2 * M := by
  rw [dyadic, intRange, Finset.mem_Ioc] at hn
  exact ⟨(Nat.floor_lt hM).1 hn.1, (Nat.le_floor_iff (by linarith)).1 hn.2⟩

/-- Lemma 6 (with `α = 1/2`, `β = 1`) counts the pairs with `|λ| ≤ t`. -/
theorem count_close {N V t C6 : ℝ} (hN : 1 ≤ N) (hV : 1 ≤ V) (ht : 0 < t)
    (hC6 : ∀ M N Δ : ℝ, 1 ≤ M → 1 ≤ N → 0 < Δ →
      (quadrupleCount (1 / 2) 1 M N Δ : ℝ) ≤ C6 * (M * N * Real.log (2 * M * N) + Δ * M ^ 2 * N ^ 2)) :
    (((pairSet V N).filter (fun p => |lamOf p| ≤ t)).card : ℝ) ≤
      C6 * (N * V * Real.log (2 * N * V) + (4 * t * V / Real.sqrt N) * N ^ 2 * V ^ 2) := by
  classical
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have hΔ : 0 < 4 * t * V / Real.sqrt N := by positivity
  refine le_trans ?_ (hC6 N V _ hN hV hΔ)
  unfold quadrupleCount
  apply Nat.cast_le.2
  refine Finset.card_le_card_of_injOn
    (fun p : (ℕ × ℕ) × (ℕ × ℕ) => (p.2.2, p.1.2, p.2.1, p.1.1)) ?_ ?_
  · intro p hp
    replace hp : p ∈ (pairSet V N).filter (fun p => |lamOf p| ≤ t) := hp
    rw [Finset.mem_filter, pairSet, Finset.mem_product, Finset.mem_product,
      Finset.mem_product] at hp
    obtain ⟨⟨⟨hv1, hn1⟩, ⟨hv2, hn2⟩⟩, hlam⟩ := hp
    show (p.2.2, p.1.2, p.2.1, p.1.1) ∈ Finset.filter _ _
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_product]
    refine ⟨⟨dyadic_subset_closedRange (by linarith) hn2, dyadic_subset_closedRange (by linarith) hn1,
      dyadic_subset_closedRange (by linarith) hv2, dyadic_subset_closedRange (by linarith) hv1⟩, ?_⟩
    -- the spacing condition
    obtain ⟨hv1a, hv1b⟩ := mem_dyadic_bounds (by linarith) hv1
    obtain ⟨hv2a, hv2b⟩ := mem_dyadic_bounds (by linarith) hv2
    obtain ⟨hn1a, hn1b⟩ := mem_dyadic_bounds (by linarith) hn1
    obtain ⟨hn2a, hn2b⟩ := mem_dyadic_bounds (by linarith) hn2
    have hv10 : (0 : ℝ) < p.1.1 := by linarith
    have hv20 : (0 : ℝ) < p.2.1 := by linarith
    have hn20 : (0 : ℝ) < p.2.2 := by linarith
    have hsn2 : Real.sqrt N ≤ Real.sqrt p.2.2 := Real.sqrt_le_sqrt hn2a.le
    have hsn20 : 0 < Real.sqrt p.2.2 := lt_of_lt_of_le hsN hsn2
    show |((p.1.2 : ℝ) / p.2.2) ^ ((1 : ℝ) / 2) - ((p.1.1 : ℝ) / p.2.1) ^ (1 : ℝ)| <
      4 * t * V / Real.sqrt N
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ hn20.le, Real.rpow_one]
    have e : Real.sqrt p.1.2 / Real.sqrt p.2.2 - (p.1.1 : ℝ) / p.2.1 =
        ((p.1.1 : ℝ) / Real.sqrt p.2.2) * lamOf p := by
      unfold lamOf
      first | (field_simp; done) | (field_simp; ring)
    rw [e, abs_mul, abs_of_pos (div_pos hv10 hsn20)]
    have hfrac : (p.1.1 : ℝ) / Real.sqrt p.2.2 ≤ 2 * V / Real.sqrt N := by
      rw [div_le_div_iff₀ hsn20 hsN]
      exact mul_le_mul hv1b hsn2 hsN.le (by linarith)
    calc (p.1.1 : ℝ) / Real.sqrt p.2.2 * |lamOf p| ≤ 2 * V / Real.sqrt N * t :=
          mul_le_mul hfrac hlam (abs_nonneg _) (by positivity)
      _ = 2 * t * V / Real.sqrt N := by ring
      _ < 4 * t * V / Real.sqrt N := by
          apply div_lt_div_of_pos_right _ hsN
          nlinarith [mul_pos ht (by linarith : (0 : ℝ) < V)]
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Prod.ext h.2.2.2 h.2.1) (Prod.ext h.2.2.1 h.1)

end L9

end LeanProofs.IntegerPoints
