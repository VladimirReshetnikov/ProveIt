import IntegerPoints.GKLemma31

/-!
# Graham–Kolesnik, Lemma 3.2 (the second-derivative test for integrals)

If `|f''| ≥ λ₂ > 0` on `[a, b]` then `|∫_a^b e(f)| ≤ C λ₂^{-1/2}`.

Proof.  `f''` has constant sign; replacing `f` by `-f` (which conjugates `e(f)`)
we may assume `f'' ≥ λ₂`, so `f'` is increasing.  With `λ = √λ₂` split `[a, b]`
at the points `c ≤ d` where `f'` crosses `-λ` and `λ` (intermediate value
theorem; `c = a` if `f'(a) ≥ -λ`, `d = b` if `f'(b) ≤ λ`).  On `[a, c]` and
`[d, b]` we have `|f'| ≥ λ` and `1/f'` is monotone, so Lemma 3.1 gives `≤ C₁/λ`
each; on `[c, d]` the trivial bound and `λ₂(d - c) ≤ f'(d) - f'(c) ≤ 2λ` give
`≤ 2λ/λ₂ = 2/λ`.  Altogether `≤ (2C₁ + 2) λ₂^{-1/2}`.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace GK32

/-- The hypothesis form of Lemma 3.1 with constant `C₁`. -/
def L31 (C₁ : ℝ) : Prop :=
  ∀ (a b lam : ℝ) (f g : ℝ → ℝ), a ≤ b → 0 < lam →
    ContDiff ℝ 2 f → ContDiff ℝ 2 g →
    (MonotoneOn (fun x => g x / deriv f x) (Set.Icc a b) ∨
      AntitoneOn (fun x => g x / deriv f x) (Set.Icc a b)) →
    (∀ x ∈ Set.Icc a b, deriv f x ≠ 0 ∧ lam * |g x| ≤ |deriv f x|) →
    ‖∫ x in a..b, (g x : ℂ) * e (f x)‖ ≤ C₁ / lam

/-- The constant of Lemma 3.1 is nonnegative (apply it to `f = id`, `g = 1` on `[0, 1]`). -/
theorem L31_nonneg {C₁ : ℝ} (h : L31 C₁) : 0 ≤ C₁ := by
  have := h 0 1 1 id (fun _ => 1) zero_le_one one_pos contDiff_id contDiff_const
    (Or.inl (by
      intro x _ y _ _
      simp))
    (fun x _ => by simp)
  have h0 : (0 : ℝ) ≤ ‖∫ x in (0 : ℝ)..1, ((fun _ => (1 : ℝ)) x : ℂ) * e (id x)‖ := norm_nonneg _
  rw [div_one] at this
  linarith

/-- `e(-t) = conj (e t)`, so conjugation flips the sign of the phase. -/
theorem integral_e_neg (f : ℝ → ℝ) (a b : ℝ) :
    ∫ x in a..b, e (-f x) = starRingEnd ℂ (∫ x in a..b, e (f x)) := by
  have h : ∀ x, e (-f x) = starRingEnd ℂ (e (f x)) := fun x => KL.e_neg (f x)
  simp_rw [h]
  simp only [intervalIntegral, map_sub, integral_conj]

theorem continuous_e_comp {f : ℝ → ℝ} (hf : Continuous f) : Continuous fun x => e (f x) := by
  unfold e
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hf))

/-- Lemma 3.1 with `g = 1` on an interval where `|f'| ≥ λ` and `f'' ≥ 0`:
`1/f'` is antitone there. -/
theorem piece_bound {C₁ : ℝ} (h31 : L31 C₁) {a b lam : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hlam : 0 < lam) (hf : ContDiff ℝ 2 f)
    (hf'' : ∀ x ∈ Set.Icc a b, 0 ≤ deriv (deriv f) x)
    (hbig : ∀ x ∈ Set.Icc a b, lam ≤ |deriv f x|) :
    ‖∫ x in a..b, e (f x)‖ ≤ C₁ / lam := by
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hf'd : Differentiable ℝ (deriv f) := hf1.differentiable one_ne_zero
  have hne : ∀ x ∈ Set.Icc a b, deriv f x ≠ 0 := by
    intro x hx h0
    have := hbig x hx
    rw [h0, abs_zero] at this
    linarith
  have hanti : AntitoneOn (fun x => (fun _ : ℝ => (1 : ℝ)) x / deriv f x) (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
    · exact ContinuousOn.div continuousOn_const hf1.continuous.continuousOn (fun x hx => hne x hx)
    · intro x hx
      rw [interior_Icc] at hx
      exact ((differentiableAt_const _).div (hf'd x)
        (hne x ⟨hx.1.le, hx.2.le⟩)).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Set.Icc a b := ⟨hx.1.le, hx.2.le⟩
      have hd : HasDerivAt (fun y => (fun _ : ℝ => (1 : ℝ)) y / deriv f y)
          ((0 * deriv f x - 1 * deriv (deriv f) x) / (deriv f x) ^ 2) x :=
        (hasDerivAt_const x (1 : ℝ)).div (hf'd x).hasDerivAt (hne x hx')
      rw [hd.deriv]
      have h2 := hf'' x hx'
      have h3 : 0 < (deriv f x) ^ 2 := by have := hne x hx'; positivity
      apply div_nonpos_of_nonpos_of_nonneg _ h3.le
      linarith
  have := h31 a b lam f (fun _ => 1) hab hlam hf contDiff_const (Or.inr hanti)
    (fun x hx => ⟨hne x hx, by simpa using hbig x hx⟩)
  simpa using this

/-- The core estimate for `f'' ≥ λ₂`: `‖∫ e(f)‖ ≤ (2C₁ + 2) λ₂^{-1/2}`. -/
theorem core {C₁ : ℝ} (h31 : L31 C₁) {a b lam₂ : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hlam₂ : 0 < lam₂) (hf : ContDiff ℝ 2 f)
    (hf'' : ∀ x ∈ Set.Icc a b, lam₂ ≤ deriv (deriv f) x) :
    ‖∫ x in a..b, e (f x)‖ ≤ (2 * C₁ + 2) * lam₂ ^ (-(1 : ℝ) / 2) := by
  have hC₁ := L31_nonneg h31
  set lam : ℝ := Real.sqrt lam₂ with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.2 hlam₂
  have hlam2 : lam * lam = lam₂ := Real.mul_self_sqrt hlam₂.le
  have hrpow : lam₂ ^ (-(1 : ℝ) / 2) = 1 / lam := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hlam₂.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hrpow]
  have hC : 0 ≤ C₁ / lam := by positivity
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf)).2.2
  have hf'c : ContinuousOn (deriv f) (Set.Icc a b) := hf1.continuous.continuousOn
  have hf'd : Differentiable ℝ (deriv f) := hf1.differentiable one_ne_zero
  have hf''0 : ∀ x ∈ Set.Icc a b, 0 ≤ deriv (deriv f) x := fun x hx => hlam₂.le.trans (hf'' x hx)
  set F := deriv f with hF
  -- `f'` grows at least linearly, in particular it is monotone
  have hgrow : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → lam₂ * (y - x) ≤ F y - F x := by
    intro x hx y hy hxy
    exact Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc a b) hf'c
      hf'd.differentiableOn (fun z hz => by
        rw [interior_Icc] at hz
        exact hf'' z ⟨hz.1.le, hz.2.le⟩) x hx y hy hxy
  have hmono : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y → F x ≤ F y := by
    intro x hx y hy hxy
    have := hgrow x hx y hy hxy
    nlinarith
  have hec : Continuous fun x => e (f x) := continuous_e_comp hf.continuous
  -- a piece `[p, q] ⊆ [a, b]` with `|f'| ≥ λ`
  have hpiece : ∀ p q, a ≤ p → p ≤ q → q ≤ b → (∀ x ∈ Set.Icc p q, lam ≤ |F x|) →
      ‖∫ x in p..q, e (f x)‖ ≤ C₁ / lam := by
    intro p q hap hpq hqb hbig
    exact piece_bound h31 hpq hlam0 hf
      (fun x hx => hf''0 x ⟨hap.trans hx.1, hx.2.trans hqb⟩) hbig
  -- the trivial bound on a piece
  have htriv : ∀ p q, p ≤ q → ‖∫ x in p..q, e (f x)‖ ≤ q - p := by
    intro p q hpq
    have := norm_integral_le_of_norm_le_const (a := p) (b := q) (C := 1)
      (f := fun x => e (f x)) (fun x _ => by rw [norm_e])
    rw [one_mul, abs_of_nonneg (by linarith)] at this
    exact this
  rcases le_or_gt (F b) (-lam) with hFb | hFb
  · -- Case 1: `f' ≤ -λ` throughout
    have := hpiece a b le_rfl hab le_rfl (fun x hx => by
      have := hmono x hx b ⟨hab, le_rfl⟩ hx.2
      rw [abs_of_neg (by linarith)]
      linarith)
    calc _ ≤ C₁ / lam := this
      _ ≤ (2 * C₁ + 2) * (1 / lam) := by
          rw [div_eq_mul_one_div]
          have : 0 ≤ 1 / lam := by positivity
          nlinarith
  rcases le_or_gt lam (F a) with hFa | hFa
  · -- Case 2: `f' ≥ λ` throughout
    have := hpiece a b le_rfl hab le_rfl (fun x hx => by
      have := hmono a ⟨le_rfl, hab⟩ x hx hx.1
      rw [abs_of_pos (by linarith)]
      linarith)
    calc _ ≤ C₁ / lam := this
      _ ≤ (2 * C₁ + 2) * (1 / lam) := by
          rw [div_eq_mul_one_div]
          have : 0 ≤ 1 / lam := by positivity
          nlinarith
  -- Case 3: `f'(b) > -λ` and `f'(a) < λ`; split at `c ≤ d`
  obtain ⟨c, hac, hcb, hFc, hleft⟩ : ∃ c, a ≤ c ∧ c ≤ b ∧ -lam ≤ F c ∧
      (c = a ∨ (F c = -lam ∧ ∀ x ∈ Set.Icc a c, lam ≤ |F x|)) := by
    rcases le_or_gt (-lam) (F a) with h | h
    · exact ⟨a, le_rfl, hab, h, Or.inl rfl⟩
    · obtain ⟨c, hc, hFc⟩ := intermediate_value_Icc hab hf'c ⟨h.le, hFb.le⟩
      refine ⟨c, hc.1, hc.2, hFc.symm.le, Or.inr ⟨hFc, fun x hx => ?_⟩⟩
      have := hmono x ⟨hx.1, hx.2.trans hc.2⟩ c hc hx.2
      rw [abs_of_neg (by linarith)]
      linarith
  obtain ⟨d, had, hdb, hFd, hright⟩ : ∃ d, a ≤ d ∧ d ≤ b ∧ F d ≤ lam ∧
      (d = b ∨ (F d = lam ∧ ∀ x ∈ Set.Icc d b, lam ≤ |F x|)) := by
    rcases le_or_gt (F b) lam with h | h
    · exact ⟨b, hab, le_rfl, h, Or.inl rfl⟩
    · obtain ⟨d, hd, hFd⟩ := intermediate_value_Icc hab hf'c ⟨hFa.le, h.le⟩
      refine ⟨d, hd.1, hd.2, hFd.le, Or.inr ⟨hFd, fun x hx => ?_⟩⟩
      have := hmono d hd x ⟨hd.1.trans hx.1, hx.2⟩ hx.1
      rw [abs_of_pos (by linarith)]
      linarith
  have hcd : c ≤ d := by
    by_contra hlt
    push Not at hlt
    rcases hleft with hc | hc
    · subst hc; linarith
    rcases hright with hd | hd
    · subst hd; linarith
    have := hmono d ⟨had, hdb⟩ c ⟨hac, hcb⟩ hlt.le
    rw [hd.1, hc.1] at this
    linarith
  -- split the integral
  have hi1 : IntervalIntegrable (fun x => e (f x)) volume a c := hec.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => e (f x)) volume c d := hec.intervalIntegrable _ _
  have hi3 : IntervalIntegrable (fun x => e (f x)) volume d b := hec.intervalIntegrable _ _
  have hsplit : ∫ x in a..b, e (f x) =
      (∫ x in a..c, e (f x)) + (∫ x in c..d, e (f x)) + ∫ x in d..b, e (f x) := by
    rw [integral_add_adjacent_intervals hi1 hi2, integral_add_adjacent_intervals
      (hi1.trans hi2) hi3]
  -- the three pieces
  have hp1 : ‖∫ x in a..c, e (f x)‖ ≤ C₁ / lam := by
    rcases hleft with hc | hc
    · subst hc; rw [intervalIntegral.integral_same, norm_zero]; exact hC
    · exact hpiece a c le_rfl hac hcb hc.2
  have hp3 : ‖∫ x in d..b, e (f x)‖ ≤ C₁ / lam := by
    rcases hright with hd | hd
    · subst hd; rw [intervalIntegral.integral_same, norm_zero]; exact hC
    · exact hpiece d b had hdb le_rfl hd.2
  have hp2 : ‖∫ x in c..d, e (f x)‖ ≤ 2 / lam := by
    refine (htriv c d hcd).trans ?_
    have h1 := hgrow c ⟨hac, hcb⟩ d ⟨had, hdb⟩ hcd
    have h2 : F d - F c ≤ 2 * lam := by linarith
    rw [le_div_iff₀ hlam0]
    nlinarith
  rw [hsplit]
  calc ‖(∫ x in a..c, e (f x)) + (∫ x in c..d, e (f x)) + ∫ x in d..b, e (f x)‖
      ≤ ‖(∫ x in a..c, e (f x)) + (∫ x in c..d, e (f x))‖ + ‖∫ x in d..b, e (f x)‖ :=
        norm_add_le _ _
    _ ≤ ‖∫ x in a..c, e (f x)‖ + ‖∫ x in c..d, e (f x)‖ + ‖∫ x in d..b, e (f x)‖ := by
        linarith [norm_add_le (∫ x in a..c, e (f x)) (∫ x in c..d, e (f x))]
    _ ≤ C₁ / lam + 2 / lam + C₁ / lam := add_le_add (add_le_add hp1 hp2) hp3
    _ = (2 * C₁ + 2) * (1 / lam) := by ring

end GK32

/-- **Graham–Kolesnik, Lemma 3.2** holds. -/
theorem gk_lemma32_holds : gk_lemma32 := by
  obtain ⟨C₁, h31⟩ := gk_lemma31_holds
  have h31' : GK32.L31 C₁ := h31
  refine ⟨2 * C₁ + 2, fun a b lam₂ f hab hlam₂ hf hf'' => ?_⟩
  have hf2c : Continuous (iteratedDeriv 2 f) := hf.continuous_iteratedDeriv' 2
  -- `f''` has constant sign
  have hsign : (∀ x ∈ Set.Icc a b, lam₂ ≤ iteratedDeriv 2 f x) ∨
      (∀ x ∈ Set.Icc a b, iteratedDeriv 2 f x ≤ -lam₂) := by
    have hcases : ∀ x ∈ Set.Icc a b, lam₂ ≤ iteratedDeriv 2 f x ∨ iteratedDeriv 2 f x ≤ -lam₂ := by
      intro x hx
      have := hf'' x hx
      rcases le_or_gt 0 (iteratedDeriv 2 f x) with h0 | h0
      · left; rwa [abs_of_nonneg h0] at this
      · right; rw [abs_of_neg h0] at this; linarith
    rcases hcases a ⟨le_rfl, hab⟩ with ha | ha
    · left
      intro x hx
      rcases hcases x hx with h | h
      · exact h
      · exfalso
        obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hx.1 hf2c.continuousOn
          (show (0 : ℝ) ∈ Set.Icc (iteratedDeriv 2 f x) (iteratedDeriv 2 f a) from
            ⟨by linarith, by linarith⟩)
        have := hf'' z ⟨hz.1, hz.2.trans hx.2⟩
        rw [hz0, abs_zero] at this
        linarith
    · right
      intro x hx
      rcases hcases x hx with h | h
      · exfalso
        obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hx.1 hf2c.continuousOn
          (show (0 : ℝ) ∈ Set.Icc (iteratedDeriv 2 f a) (iteratedDeriv 2 f x) from
            ⟨by linarith, by linarith⟩)
        have := hf'' z ⟨hz.1, hz.2.trans hx.2⟩
        rw [hz0, abs_zero] at this
        linarith
      · exact h
  rcases hsign with hpos | hneg
  · exact GK32.core h31' hab hlam₂ hf (fun x hx => by
      have := hpos x hx
      rwa [iteratedDeriv_succ, iteratedDeriv_one] at this)
  · -- apply the core to `-f`
    have hneg' : ∀ x ∈ Set.Icc a b, lam₂ ≤ deriv (deriv (-f)) x := by
      intro x hx
      have := hneg x hx
      rw [iteratedDeriv_succ, iteratedDeriv_one] at this
      have e1 : deriv (deriv (-f)) x = -deriv (deriv f) x := by
        have : deriv (-f) = -deriv f := by
          funext y
          exact deriv.neg
        rw [this, deriv.neg]
      rw [e1]
      linarith
    have := GK32.core h31' hab hlam₂ hf.neg hneg'
    have e2 : ∫ x in a..b, e (-f x) = starRingEnd ℂ (∫ x in a..b, e (f x)) :=
      GK32.integral_e_neg f a b
    rw [e2, Complex.norm_conj] at this
    exact this

end LeanProofs.IntegerPoints
