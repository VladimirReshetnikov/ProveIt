import IntegerPoints.VanDerCorput

/-!
# Zhai–Cao, Lemma 1

`zhaiCao_lemma1` follows from the Kuz'min–Landau inequality (when
`c₂ λ₁ ≤ 1/2`) and the van der Corput second-derivative test (otherwise),
after normalising the sign of `f''` (which is constant on the interval by
continuity) with the substitution `f ↦ -f`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace Lemma1

/-- A continuous function that never vanishes on `[a, b]` has constant sign. -/
theorem sign_const {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : ContinuousOn g (Set.Icc a b))
    (hne : ∀ t ∈ Set.Icc a b, g t ≠ 0) :
    (∀ t ∈ Set.Icc a b, 0 < g t) ∨ (∀ t ∈ Set.Icc a b, g t < 0) := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  rcases lt_or_gt_of_ne (hne a ha) with h | h
  · right
    intro t ht
    by_contra hcon
    push Not at hcon
    have hsub : Set.uIcc a t ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le ht.1]
      exact Set.Icc_subset_Icc le_rfl ht.2
    obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc (hg.mono hsub)
      (show (0 : ℝ) ∈ Set.uIcc (g a) (g t) from Set.mem_uIcc.2 (Or.inl ⟨h.le, hcon⟩))
    exact hne s (hsub hs) hs0
  · left
    intro t ht
    by_contra hcon
    push Not at hcon
    have hsub : Set.uIcc a t ⊆ Set.Icc a b := by
      rw [Set.uIcc_of_le ht.1]
      exact Set.Icc_subset_Icc le_rfl ht.2
    obtain ⟨s, hs, hs0⟩ := intermediate_value_uIcc (hg.mono hsub)
      (show (0 : ℝ) ∈ Set.uIcc (g a) (g t) from Set.mem_uIcc.2 (Or.inr ⟨hcon, h.le⟩))
    exact hne s (hsub hs) hs0

/-- `‖x‖ ≥ δ` when `δ ≤ |x| ≤ 1/2` and `δ ≤ 1/2`. -/
theorem nearestIntDist_ge_of_abs {x δ : ℝ} (hδ : δ ≤ 1 / 2) (h1 : δ ≤ |x|) (h2 : |x| ≤ 1 / 2) :
    δ ≤ nearestIntDist x := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at h1 h2
    exact VdC.nearestIntDist_ge 0 (by push_cast; linarith) (by push_cast; linarith)
  · rw [abs_of_neg h] at h1 h2
    exact VdC.nearestIntDist_ge (-1) (by push_cast; linarith) (by push_cast; linarith)

theorem norm_sum_e_neg (s : Finset ℕ) (f : ℝ → ℝ) :
    ‖∑ n ∈ s, e (-f n)‖ = ‖∑ n ∈ s, e (f n)‖ := by
  have : ∑ n ∈ s, e (-f n) = starRingEnd ℂ (∑ n ∈ s, e (f n)) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ => KL.e_neg _
  rw [this, Complex.norm_conj]

theorem deriv2_neg (f : ℝ → ℝ) : deriv (deriv (fun t => -f t)) = fun t => -deriv (deriv f) t := by
  rw [KL.deriv_neg_fun]
  exact KL.deriv_neg_fun (deriv f)

end Lemma1

open Lemma1 in
/-- **Zhai–Cao, Lemma 1** (`zhaiCao_lemma1`). -/
theorem zhaiCao_lemma1_holds : zhaiCao_lemma1 := by
  intro c c₁ c₂ c₃ c₄ hc hc₁ hc₂ hc₃ hc₄
  have hsc₃ : 0 < Real.sqrt c₃ := Real.sqrt_pos.2 hc₃
  set C : ℝ := 4 / c₁ + 12 * (c₄ / c₃) * c * Real.sqrt c₃ + 48 * c₂ / Real.sqrt c₃ +
    2 * c * Real.sqrt c₃ with hC
  refine ⟨C, fun N lam f hN hlam hf h1 h2 => ?_⟩
  have hcN : N ≤ c * N := by nlinarith
  have hNI : N ∈ Set.Icc N (c * N) := ⟨le_rfl, hcN⟩
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h2
  -- the target quantity and its two terms
  set T : ℝ := lam⁻¹ + lam ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) with hT
  have hT1 : lam⁻¹ ≤ T := by
    have : 0 ≤ lam ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) := by positivity
    linarith
  have hT2 : Real.sqrt lam * Real.sqrt N ≤ T := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    have : 0 ≤ lam⁻¹ := by positivity
    linarith
  have hT0 : 0 ≤ T := le_trans (by positivity) hT1
  -- the main estimate for `g` with `g'' > 0`
  suffices key : ∀ g : ℝ → ℝ, ContDiff ℝ 2 g →
      (∀ t ∈ Set.Icc N (c * N), c₁ * lam ≤ |deriv g t| ∧ |deriv g t| ≤ c₂ * lam) →
      (∀ t ∈ Set.Icc N (c * N), c₃ * lam / N ≤ deriv (deriv g) t ∧
        deriv (deriv g) t ≤ c₄ * lam / N) →
      ‖∑ n ∈ intRange N (c * N), e (g n)‖ ≤ C * T by
    have hf' : ContDiff ℝ 1 (deriv f) :=
      (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
    have hcont2 : ContinuousOn (deriv (deriv f)) (Set.Icc N (c * N)) :=
      (hf'.continuous_deriv le_rfl).continuousOn
    have hne : ∀ t ∈ Set.Icc N (c * N), deriv (deriv f) t ≠ 0 := by
      intro t ht h0
      have := (h2 t ht).1
      rw [h0, abs_zero] at this
      have : 0 < c₃ * lam / N := by positivity
      linarith
    rcases sign_const hcN hcont2 hne with hpos | hneg
    · exact key f hf h1 fun t ht => by
        have := h2 t ht
        rwa [abs_of_pos (hpos t ht)] at this
    · have := key (fun t => -f t) hf.neg
        (fun t ht => by rw [KL.deriv_neg_fun]; simp only [abs_neg]; exact h1 t ht)
        (fun t ht => by
          rw [deriv2_neg]
          simp only
          have := h2 t ht
          rw [abs_of_neg (hneg t ht)] at this
          exact ⟨this.1, this.2⟩)
      rwa [norm_sum_e_neg] at this
  intro g hg hg1 hg2
  have hg' : ContDiff ℝ 1 (deriv g) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) g from hg)).2.2
  have hg1' : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  -- the summation range
  set A := ⌊N⌋₊ with hA
  set B := ⌊c * N⌋₊ with hB
  have hrange : intRange N (c * N) = Finset.Ioc A B := rfl
  have hAN : (A : ℝ) ≤ N := Nat.floor_le (by linarith)
  have hNA : N < A + 1 := Nat.lt_floor_add_one N
  have hBcN : (B : ℝ) ≤ c * N := Nat.floor_le (by positivity)
  have hsub : Set.Icc (A + 1 : ℝ) B ⊆ Set.Icc N (c * N) :=
    Set.Icc_subset_Icc hNA.le hBcN
  have hBA : ((B - A : ℕ) : ℝ) ≤ c * N := by
    rcases le_or_gt A B with h | h
    · rw [Nat.cast_sub h]
      linarith [(Nat.lt_floor_add_one N), hAN]
    · rw [Nat.sub_eq_zero_of_le h.le]
      push_cast
      positivity
  have hmono : MonotoneOn (deriv g) (Set.Icc (A + 1 : ℝ) B) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hg'.continuous.continuousOn
      (hg'.differentiable one_ne_zero).differentiableOn fun x hx => ?_
    rw [interior_Icc] at hx
    have := (hg2 x (hsub ⟨hx.1.le, hx.2.le⟩)).1
    have : 0 < c₃ * lam / N := by positivity
    linarith
  rw [hrange]
  have hC1 : 4 / c₁ ≤ C := by
    rw [hC]
    have : 0 ≤ 12 * (c₄ / c₃) * c * Real.sqrt c₃ := by positivity
    have : 0 ≤ 48 * c₂ / Real.sqrt c₃ := by positivity
    have : 0 ≤ 2 * c * Real.sqrt c₃ := by positivity
    linarith
  have hC2 : 12 * (c₄ / c₃) * c * Real.sqrt c₃ + 48 * c₂ / Real.sqrt c₃ ≤ C := by
    rw [hC]
    have : 0 ≤ 4 / c₁ := by positivity
    have : 0 ≤ 2 * c * Real.sqrt c₃ := by positivity
    linarith
  have hC3 : 2 * c * Real.sqrt c₃ ≤ C := by
    rw [hC]
    have : 0 ≤ 4 / c₁ := by positivity
    have : 0 ≤ 12 * (c₄ / c₃) * c * Real.sqrt c₃ := by positivity
    have : 0 ≤ 48 * c₂ / Real.sqrt c₃ := by positivity
    linarith
  rcases le_or_gt (c₂ * lam) (1 / 2) with hreg | hreg
  · -- Kuz'min–Landau regime
    have hc12 : c₁ ≤ c₂ := by
      have := hg1 N hNI
      nlinarith
    have hl1 : 0 < c₁ * lam := by positivity
    have hl2 : c₁ * lam ≤ 1 / 2 := le_trans (by nlinarith) hreg
    have hKL := KL.kuzmin_landau g A B (c₁ * lam) hl1 hl2 hg1' (Or.inl hmono) fun t ht => by
      have := hg1 t (hsub ht)
      exact nearestIntDist_ge_of_abs hl2 this.1 (le_trans this.2 hreg)
    calc ‖∑ n ∈ Finset.Ioc A B, e (g n)‖ ≤ 4 / (c₁ * lam) := hKL
      _ = (4 / c₁) * lam⁻¹ := by field_simp
      _ ≤ C * T := mul_le_mul hC1 hT1 (by positivity) (le_trans (by positivity) hC1)
  · -- second-derivative regime
    have hlam2 : 1 / lam < 2 * c₂ := by
      rw [div_lt_iff₀ hlam]
      linarith
    set lam2 := c₃ * lam / N with hlam2def
    have hl2pos : 0 < lam2 := by positivity
    have hsqrt : Real.sqrt lam2 = Real.sqrt c₃ * Real.sqrt lam / Real.sqrt N := by
      rw [hlam2def, Real.sqrt_div (by positivity), Real.sqrt_mul hc₃.le]
    have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
    have hsl : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
    have hsN2 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (by linarith)
    have hsl2 : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam.le
    have hsc2 : Real.sqrt c₃ * Real.sqrt c₃ = c₃ := Real.mul_self_sqrt hc₃.le
    rcases le_or_gt lam2 (1 / 4) with hsmall | hbig
    · have hα : 0 ≤ c₄ / c₃ := by positivity
      have hvdc := VdC.second_derivative g hg A B lam2 (c₄ / c₃) hl2pos hsmall hα fun t ht => by
        have := hg2 t (hsub ht)
        refine ⟨this.1, ?_⟩
        calc deriv (deriv g) t ≤ c₄ * lam / N := this.2
          _ = c₄ / c₃ * lam2 := by
              rw [hlam2def]
              field_simp
      -- algebra
      have hterm1 : 12 * (c₄ / c₃) * ((B - A : ℕ) : ℝ) * Real.sqrt lam2 ≤
          12 * (c₄ / c₃) * c * Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) := by
        rw [hsqrt]
        have h1 : 12 * (c₄ / c₃) * ((B - A : ℕ) : ℝ) * (Real.sqrt c₃ * Real.sqrt lam / Real.sqrt N) ≤
            12 * (c₄ / c₃) * (c * N) * (Real.sqrt c₃ * Real.sqrt lam / Real.sqrt N) := by
          gcongr
        refine le_trans h1 (le_of_eq ?_)
        have hNs : N / Real.sqrt N = Real.sqrt N := by
          rw [div_eq_iff hsN.ne']
          exact hsN2.symm
        calc 12 * (c₄ / c₃) * (c * N) * (Real.sqrt c₃ * Real.sqrt lam / Real.sqrt N)
            = 12 * (c₄ / c₃) * c * Real.sqrt c₃ * Real.sqrt lam * (N / Real.sqrt N) := by ring
          _ = 12 * (c₄ / c₃) * c * Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) := by
              rw [hNs]
              ring
      have hterm2 : 24 / Real.sqrt lam2 ≤ 48 * c₂ / Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) := by
        rw [hsqrt]
        have hls : Real.sqrt lam / lam = 1 / Real.sqrt lam := by
          rw [div_eq_div_iff hlam.ne' hsl.ne', one_mul]
          exact hsl2
        have : 24 / (Real.sqrt c₃ * Real.sqrt lam / Real.sqrt N) =
            24 / Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) * (1 / lam) := by
          calc 24 / (Real.sqrt c₃ * Real.sqrt lam / Real.sqrt N)
              = 24 / Real.sqrt c₃ * Real.sqrt N * (1 / Real.sqrt lam) := by
                field_simp
            _ = 24 / Real.sqrt c₃ * Real.sqrt N * (Real.sqrt lam / lam) := by rw [hls]
            _ = 24 / Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) * (1 / lam) := by ring
        rw [this]
        have hpos : 0 ≤ 24 / Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) := by positivity
        calc 24 / Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) * (1 / lam)
            ≤ 24 / Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) * (2 * c₂) :=
              mul_le_mul_of_nonneg_left hlam2.le hpos
          _ = 48 * c₂ / Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) := by ring
      calc ‖∑ n ∈ Finset.Ioc A B, e (g n)‖
          ≤ 12 * (c₄ / c₃) * ((B - A : ℕ) : ℝ) * Real.sqrt lam2 + 24 / Real.sqrt lam2 := hvdc
        _ ≤ (12 * (c₄ / c₃) * c * Real.sqrt c₃ + 48 * c₂ / Real.sqrt c₃) *
              (Real.sqrt lam * Real.sqrt N) := by
            rw [add_mul]
            exact add_le_add hterm1 hterm2
        _ ≤ C * T := mul_le_mul hC2 hT2 (by positivity) (le_trans (by positivity) hC2)
    · -- trivial bound: `λ₂ > 1/4` forces `N < 2 √c₃ √(λ N)`
      have hcard : ‖∑ n ∈ Finset.Ioc A B, e (g n)‖ ≤ ((B - A : ℕ) : ℝ) := by
        calc ‖∑ n ∈ Finset.Ioc A B, e (g n)‖ ≤ ∑ n ∈ Finset.Ioc A B, ‖e (g n)‖ := norm_sum_le _ _
          _ = ((B - A : ℕ) : ℝ) := by simp [norm_e]
      have hNbound : N ≤ 2 * Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) := by
        -- `1/4 < c₃ λ / N`, i.e. `N < 4 c₃ λ`, i.e. `√N < 2 √c₃ √λ`
        have h1 : N < 4 * c₃ * lam := by
          rw [hlam2def, lt_div_iff₀ (by linarith)] at hbig
          linarith
        have h2 : Real.sqrt N ≤ 2 * Real.sqrt c₃ * Real.sqrt lam := by
          have : Real.sqrt N ≤ Real.sqrt (4 * c₃ * lam) := Real.sqrt_le_sqrt h1.le
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
            show Real.sqrt 4 = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
          linarith
        calc N = Real.sqrt N * Real.sqrt N := hsN2.symm
          _ ≤ (2 * Real.sqrt c₃ * Real.sqrt lam) * Real.sqrt N :=
              mul_le_mul_of_nonneg_right h2 hsN.le
          _ = 2 * Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) := by ring
      calc ‖∑ n ∈ Finset.Ioc A B, e (g n)‖ ≤ ((B - A : ℕ) : ℝ) := hcard
        _ ≤ c * N := hBA
        _ ≤ c * (2 * Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N)) :=
            mul_le_mul_of_nonneg_left hNbound (by linarith)
        _ = 2 * c * Real.sqrt c₃ * (Real.sqrt lam * Real.sqrt N) := by ring
        _ ≤ C * T := mul_le_mul hC3 hT2 (by positivity) (le_trans (by positivity) hC3)

end LeanProofs.IntegerPoints
