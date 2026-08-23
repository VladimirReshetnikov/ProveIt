import IntegerPoints.Sawtooth
import Mathlib.MeasureTheory.Function.Floor

/-!
# The first-order Euler–Maclaurin formula with the sawtooth function

For a `C¹` function `F : ℝ → ℂ` and real `a ≤ b`, with `ψ(x) = x − ⌊x⌋ − 1/2`,
`∑_{a < n ≤ b} F(n) = ∫_a^b F + ψ(a) F(a) − ψ(b) F(b) + ∫_a^b ψ(x) F'(x) dx`.

Proof.  Write `Φ(p, q) = ∫_p^q F + ψ(p)F(p) − ψ(q)F(q) + ∫_p^q ψF'`; it is additive in
adjacent intervals.  If `(p, q]` contains no integer, `ψ(x) = x − ⌊p⌋ − 1/2` on
`[p, q]` and integration by parts gives `Φ(p, q) = 0`.  If `N = ⌊p⌋ + 1 ≤ q`, then on
`[p, N)` again `ψ(x) = x − ⌊p⌋ − 1/2`, and since the integral does not see the
point `N`, integration by parts gives `∫_p^N ψF' = F(N)/2 − ψ(p)F(p) − ∫_p^N F`, hence
`Φ(p, N) = F(N)` (using `ψ(N) = −1/2`).  Induction on the number of integers in
`(p, q]` finishes the proof.
-/

open Real Finset intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace EM

/-- The sawtooth function `ψ(x) = {x} − 1/2`. -/
noncomputable def ψ (x : ℝ) : ℝ := Int.fract x - 1 / 2

theorem ψ_eq_of_floor {x : ℝ} {n : ℤ} (h : ⌊x⌋ = n) : ψ x = x - n - 1 / 2 := by
  unfold ψ
  rw [Int.fract, h]

theorem ψ_intCast (n : ℤ) : ψ n = -1 / 2 := by
  unfold ψ
  simp
  norm_num

theorem abs_ψ_le (x : ℝ) : |ψ x| ≤ 1 / 2 := by
  unfold ψ
  have h1 := Int.fract_nonneg x
  have h2 := Int.fract_lt_one x
  rw [abs_le]
  constructor <;> linarith

theorem measurable_ψ : Measurable ψ := by
  unfold ψ
  exact Measurable.sub measurable_fract measurable_const

/-- `Φ(p, q) = ∫_p^q F + ψ(p)F(p) − ψ(q)F(q) + ∫_p^q ψF'`. -/
noncomputable def Φ (F F' : ℝ → ℂ) (p q : ℝ) : ℂ :=
  (∫ x in p..q, F x) + (ψ p : ℂ) * F p - (ψ q : ℂ) * F q + ∫ x in p..q, (ψ x : ℂ) * F' x

theorem intervalIntegrable_ψ_mul {F' : ℝ → ℂ} (hF'c : Continuous F') (p q : ℝ) :
    IntervalIntegrable (fun x => (ψ x : ℂ) * F' x) volume p q := by
  have hm : Measurable fun x => (ψ x : ℂ) * F' x :=
    (Complex.measurable_ofReal.comp measurable_ψ).mul hF'c.measurable
  have hb : ∃ C, ∀ x ∈ Set.uIcc p q, ‖(ψ x : ℂ) * F' x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_uIcc.image_of_continuousOn hF'c.continuousOn).isBounded.exists_norm_le
    refine ⟨1 / 2 * C, fun x hx => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := abs_ψ_le x
    have h2 := hC (F' x) ⟨x, hx, rfl⟩
    have h3 : 0 ≤ ‖F' x‖ := norm_nonneg _
    nlinarith [abs_nonneg (ψ x)]
  obtain ⟨C, hC⟩ := hb
  refine ⟨?_, ?_⟩
  · refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    apply hC
    rw [Set.mem_uIcc]
    exact Or.inl ⟨hx.1.le, hx.2⟩
  · refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    apply hC
    rw [Set.mem_uIcc]
    exact Or.inr ⟨hx.1.le, hx.2⟩

/-- Additivity of `Φ`. -/
theorem Φ_add {F F' : ℝ → ℂ} (hFc : Continuous F) (hF'c : Continuous F') (p q r : ℝ) :
    Φ F F' p r = Φ F F' p q + Φ F F' q r := by
  unfold Φ
  rw [← integral_add_adjacent_intervals (hFc.intervalIntegrable p q) (hFc.intervalIntegrable q r),
    ← integral_add_adjacent_intervals (intervalIntegrable_ψ_mul hF'c p q)
      (intervalIntegrable_ψ_mul hF'c q r)]
  ring

/-- Integration by parts against `x − n − 1/2` on `[p, q]`. -/
theorem parts {F F' : ℝ → ℂ} (hF : ∀ x, HasDerivAt F (F' x) x) (hF'c : Continuous F')
    (hFc : Continuous F) (n : ℤ) (p q : ℝ) :
    ∫ x in p..q, ((x - n - 1 / 2 : ℝ) : ℂ) * F' x =
      ((q - n - 1 / 2 : ℝ) : ℂ) * F q - ((p - n - 1 / 2 : ℝ) : ℂ) * F p - ∫ x in p..q, F x := by
  have hu : ∀ x ∈ Set.uIcc p q, HasDerivAt (fun x : ℝ => ((x - n - 1 / 2 : ℝ) : ℂ)) (1 : ℂ) x := by
    intro x _
    have := (((hasDerivAt_id x).sub_const (n : ℝ)).sub_const (1 / 2)).ofReal_comp
    simpa using this
  have hv : ∀ x ∈ Set.uIcc p q, HasDerivAt F (F' x) x := fun x _ => hF x
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (continuous_const.intervalIntegrable _ _) (hF'c.intervalIntegrable _ _)
  rw [h]
  congr 1
  apply integral_congr
  intro x _
  simp

/-- On `[p, q]` with `⌊p⌋ = ⌊q⌋ = n`, `ψ F'` integrates like `(x − n − 1/2) F'`. -/
theorem integral_ψ_eq_of_floor {F' : ℝ → ℂ} {p q : ℝ} {n : ℤ} (hpq : p ≤ q)
    (hp : ⌊p⌋ = n) (hq : q ≤ n + 1) :
    ∫ x in p..q, (ψ x : ℂ) * F' x = ∫ x in p..q, ((x - n - 1 / 2 : ℝ) : ℂ) * F' x := by
  apply intervalIntegral.integral_congr_ae
  have hnull : volume ({x : ℝ | ¬ (x ∈ Set.uIoc p q →
      (ψ x : ℂ) * F' x = ((x - n - 1 / 2 : ℝ) : ℂ) * F' x)}) = 0 := by
    apply measure_mono_null (t := {(n : ℝ) + 1})
    · intro x hx
      simp only [Set.mem_setOf_eq, Classical.not_imp] at hx
      obtain ⟨hx1, hx2⟩ := hx
      rw [Set.uIoc_of_le hpq] at hx1
      rw [Set.mem_singleton_iff]
      by_contra hne
      apply hx2
      have hfl : ⌊x⌋ = n := by
        rw [Int.floor_eq_iff]
        have h1 : (n : ℝ) ≤ p := by rw [← hp]; exact Int.floor_le p
        exact ⟨by linarith [hx1.1], lt_of_le_of_ne (hx1.2.trans hq) hne⟩
      rw [ψ_eq_of_floor hfl]
    · exact measure_singleton _
  rw [MeasureTheory.ae_iff]
  exact hnull

/-- `Φ(p, q) = 0` when `(p, q]` contains no integer. -/
theorem Φ_eq_zero {F F' : ℝ → ℂ} (hF : ∀ x, HasDerivAt F (F' x) x) (hF'c : Continuous F')
    (hFc : Continuous F) {p q : ℝ} (hpq : p ≤ q) (h : ⌊q⌋ = ⌊p⌋) : Φ F F' p q = 0 := by
  unfold Φ
  have hq1 : q < ⌊p⌋ + 1 := by rw [← h]; exact Int.lt_floor_add_one q
  rw [integral_ψ_eq_of_floor hpq rfl hq1.le, parts hF hF'c hFc ⌊p⌋ p q,
    ψ_eq_of_floor (x := p) rfl, ψ_eq_of_floor (x := q) h]
  ring

/-- `Φ(p, N) = F(N)` when `N = ⌊p⌋ + 1`. -/
theorem Φ_eq_F {F F' : ℝ → ℂ} (hF : ∀ x, HasDerivAt F (F' x) x) (hF'c : Continuous F')
    (hFc : Continuous F) (p : ℝ) : Φ F F' p (⌊p⌋ + 1) = F (⌊p⌋ + 1) := by
  unfold Φ
  have hp1 : p ≤ (⌊p⌋ : ℝ) + 1 := (Int.lt_floor_add_one p).le
  rw [integral_ψ_eq_of_floor hp1 rfl le_rfl, parts hF hF'c hFc ⌊p⌋ p _,
    ψ_eq_of_floor (x := p) rfl, show ((⌊p⌋ : ℝ) + 1) = ((⌊p⌋ + 1 : ℤ) : ℝ) by push_cast; ring,
    ψ_intCast]
  push_cast
  ring

/-- **Euler–Maclaurin, first order**: for `a ≤ b`,
`∑_{a < n ≤ b} F(n) = ∫_a^b F + ψ(a)F(a) − ψ(b)F(b) + ∫_a^b ψ F'`. -/
theorem sum_eq_Φ {F F' : ℝ → ℂ} (hF : ∀ x, HasDerivAt F (F' x) x) (hF'c : Continuous F')
    (hFc : Continuous F) :
    ∀ (k : ℕ) (a b : ℝ), a ≤ b → ⌊b⌋ = ⌊a⌋ + k →
      ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F n = Φ F F' a b := by
  intro k
  induction k with
  | zero =>
    intro a b hab hk
    simp only [Nat.cast_zero, add_zero] at hk
    rw [hk, Finset.Ioc_self, Finset.sum_empty, Φ_eq_zero hF hF'c hFc hab hk]
  | succ k ih =>
    intro a b hab hk
    set N : ℤ := ⌊a⌋ + 1 with hN
    have hNb : (N : ℝ) ≤ b := by
      have : N ≤ ⌊b⌋ := by rw [hk, hN]; push_cast; linarith
      exact (Int.le_floor.1 this)
    have haN : a ≤ N := by rw [hN]; push_cast; exact (Int.lt_floor_add_one a).le
    have hfloorN : ⌊(N : ℝ)⌋ = N := Int.floor_intCast N
    have hk' : ⌊b⌋ = ⌊(N : ℝ)⌋ + k := by rw [hfloorN, hk, hN]; push_cast; ring
    have hsplit : Finset.Ioc ⌊a⌋ ⌊b⌋ = Finset.Ioc ⌊a⌋ N ∪ Finset.Ioc N ⌊b⌋ := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by rw [hN]; omega) (by rw [hk, hN]; push_cast; omega)]
    have hdisj : Disjoint (Finset.Ioc ⌊a⌋ N) (Finset.Ioc N ⌊b⌋) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_Ioc] at hx1 hx2
      omega
    have hsingle : Finset.Ioc ⌊a⌋ N = {N} := by
      ext x
      rw [Finset.mem_Ioc, Finset.mem_singleton, hN]
      omega
    have hih := ih N b hNb hk'
    rw [hfloorN] at hih
    rw [hsplit, Finset.sum_union hdisj, hsingle, Finset.sum_singleton, hih,
      Φ_add hFc hF'c a N b, hN]
    push_cast
    rw [Φ_eq_F hF hF'c hFc a]

theorem sum_eq_integral {F F' : ℝ → ℂ} (hF : ∀ x, HasDerivAt F (F' x) x) (hF'c : Continuous F')
    (hFc : Continuous F) {a b : ℝ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F n =
      (∫ x in a..b, F x) + (ψ a : ℂ) * F a - (ψ b : ℂ) * F b + ∫ x in a..b, (ψ x : ℂ) * F' x := by
  have hle : ⌊a⌋ ≤ ⌊b⌋ := Int.floor_le_floor hab
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ⌊b⌋ = ⌊a⌋ + k := ⟨(⌊b⌋ - ⌊a⌋).toNat, by omega⟩
  exact sum_eq_Φ hF hF'c hFc k a b hab hk

end EM

end LeanProofs.IntegerPoints
