import IntegerPoints.GKStatements
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Graham--Kolesnik, Lemma 3.9: local inverse foundations

This module isolates the qualitative analytic facts behind the `B`-process.
For a phase in the Graham--Kolesnik class with `s > 0` and error smaller than
one half, its first derivative is positive and its second derivative is
negative on the defining interval.  Consequently `f'` is strictly decreasing,
so the inverse data in Lemma 3.9 determine a unique point in `[a,b]`, and an
interior frequency determines an interior point.

At an interior frequency we identify the given inverse with Mathlib's local
inverse of `f'`.  This proves that it is locally `C^(P-1)` without imposing any
global regularity hypothesis on the inverse function.  Finally, differentiating
the Legendre identity `phi nu = nu * x nu - f (x nu)` gives `phi' = x` on the
open derivative interval.
-/

open Real Finset Set Filter

namespace LeanProofs.IntegerPoints

namespace GK39

/-! ### Signs and strict monotonicity -/

/-- Every point in the class interval is positive when the ambient scale is
positive. -/
theorem point_pos {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hf : InGKClass N P s y eps a b f) {t : ℝ}
    (ht : t ∈ Icc a b) : 0 < t :=
  hN.trans_le (hf.1.trans ht.1)

/-- The order-zero class inequality, rewritten as the approximation to
`f'` used below. -/
theorem abs_deriv_sub_model_lt {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hP : 2 ≤ P) (hf : InGKClass N P s y eps a b f) {t : ℝ}
    (ht : t ∈ Icc a b) :
    |deriv f t - y * t ^ (-s)| < eps * (y * t ^ (-s)) := by
  have h := hf.2.2.2.2 0 (by omega) t ht
  simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, sub_zero,
    pow_zero, zero_add, iteratedDeriv_one] at h
  calc
    |deriv f t - y * t ^ (-s)| =
        |deriv f t - 1 * 1 * y * t ^ (-s)| := by ring_nf
    _ < eps * 1 * y * t ^ (-s) := h
    _ = eps * (y * t ^ (-s)) := by ring

/-- The order-one class inequality, rewritten as the approximation to
`f''` used below. -/
theorem abs_deriv_deriv_add_model_lt {N s y eps a b : ℝ} {P : ℕ}
    {f : ℝ → ℝ} (hP : 2 ≤ P) (hf : InGKClass N P s y eps a b f)
    {t : ℝ} (ht : t ∈ Icc a b) :
    |deriv (deriv f) t + s * y * t ^ (-s - 1)| <
      eps * (s * y * t ^ (-s - 1)) := by
  have h := hf.2.2.2.2 1 (by omega) t ht
  simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero,
    add_zero, pow_one, Nat.cast_one, iteratedDeriv_succ,
    iteratedDeriv_zero] at h
  calc
    |deriv (deriv f) t + s * y * t ^ (-s - 1)| =
        |deriv (deriv f) t - -1 * s * y * t ^ (-s - 1)| := by ring_nf
    _ < eps * s * y * t ^ (-s - 1) := h
    _ = eps * (s * y * t ^ (-s - 1)) := by ring

/-- The first derivative of a Graham--Kolesnik phase is positive throughout
its class interval. -/
theorem deriv_pos_of_mem_Icc {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (_hs : 0 < s) (hy : 0 < y) (hP : 2 ≤ P)
    (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) {t : ℝ} (ht : t ∈ Icc a b) :
    0 < deriv f t := by
  have ht0 : 0 < t := point_pos hN hf ht
  have hmodel : 0 < y * t ^ (-s) := by positivity
  have heps_one : eps < 1 := by linarith
  have hsmall : eps * (y * t ^ (-s)) < y * t ^ (-s) := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right heps_one hmodel
  have happrox := abs_lt.mp (abs_deriv_sub_model_lt hP hf ht)
  linarith

/-- The second derivative of a Graham--Kolesnik phase is negative throughout
its class interval. -/
theorem deriv_deriv_neg_of_mem_Icc {N s y eps a b : ℝ} {P : ℕ}
    {f : ℝ → ℝ} (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) {t : ℝ} (ht : t ∈ Icc a b) :
    deriv (deriv f) t < 0 := by
  have ht0 : 0 < t := point_pos hN hf ht
  have hmodel : 0 < s * y * t ^ (-s - 1) := by positivity
  have heps_one : eps < 1 := by linarith
  have hsmall : eps * (s * y * t ^ (-s - 1)) <
      s * y * t ^ (-s - 1) := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right heps_one hmodel
  have happrox := abs_lt.mp (abs_deriv_deriv_add_model_lt hP hf ht)
  linarith

/-- The same second-derivative sign in the `iteratedDeriv` notation used by
`InGKClass`. -/
theorem iteratedDeriv_two_neg_of_mem_Icc {N s y eps a b : ℝ} {P : ℕ}
    {f : ℝ → ℝ} (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) {t : ℝ} (ht : t ∈ Icc a b) :
    iteratedDeriv 2 f t < 0 := by
  rw [show (2 : ℕ) = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one]
  exact deriv_deriv_neg_of_mem_Icc hN hs hy hP heps heps_half hf ht

/-- The global class regularity contains the `C^2` regularity needed for the
strict monotonicity argument. -/
theorem contDiff_two {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hP : 2 ≤ P) (hf : InGKClass N P s y eps a b f) : ContDiff ℝ 2 f :=
  hf.2.2.2.1.of_le (by exact_mod_cast hP)

/-- Since `f'' < 0`, the first derivative is strictly decreasing on the full
closed class interval. -/
theorem deriv_strictAntiOn {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) (hP : 2 ≤ P)
    (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) :
    StrictAntiOn (deriv f) (Icc a b) := by
  have hf2 : ContDiff ℝ 2 f := contDiff_two hP hf
  refine strictAntiOn_of_deriv_neg (convex_Icc a b)
    (hf2.continuous_deriv (by norm_num)).continuousOn ?_
  intro t ht
  exact deriv_deriv_neg_of_mem_Icc hN hs hy hP heps heps_half hf
    (interior_subset ht)

/-- On a nondegenerate class interval, the endpoint derivatives occur in
strict reverse order. -/
theorem deriv_endpoints_lt {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) (hP : 2 ≤ P)
    (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) (hab : a < b) :
    deriv f b < deriv f a := by
  exact deriv_strictAntiOn hN hs hy hP heps heps_half hf
    ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab

/-- The derivative interval used in Lemma 3.9 is positive and nondegenerate. -/
theorem deriv_interval_pos {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) (hP : 2 ≤ P)
    (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) (hab : a < b) :
    0 < deriv f b ∧ deriv f b < deriv f a :=
  ⟨deriv_pos_of_mem_Icc hN hs hy hP heps heps_half hf
      ⟨hab.le, le_rfl⟩,
    deriv_endpoints_lt hN hs hy hP heps heps_half hf hab⟩

/-! ### Uniqueness and interiority of the inverse data -/

/-- Any point of `[a,b]` solving the inverse equation agrees with the inverse
value specified in the hypotheses of Lemma 3.9. -/
theorem inverse_value_unique {N s y eps a b : ℝ} {P : ℕ}
    {f x : ℝ → ℝ} (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    {nu z : ℝ} (hnu : nu ∈ Icc (deriv f b) (deriv f a))
    (hz : z ∈ Icc a b) (hz_eq : deriv f z = nu) : x nu = z := by
  have hxnu := hx nu hnu
  exact (deriv_strictAntiOn hN hs hy hP heps heps_half hf).injOn
    hxnu.1 hz (hxnu.2.trans hz_eq.symm)

/-- Two functions satisfying the inverse data agree throughout the closed
derivative interval. -/
theorem inverse_data_unique {N s y eps a b : ℝ} {P : ℕ}
    {f x z : ℝ → ℝ} (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hz : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      z nu ∈ Icc a b ∧ deriv f (z nu) = nu) :
    Set.EqOn x z (Icc (deriv f b) (deriv f a)) := by
  intro nu hnu
  exact inverse_value_unique hN hs hy hP heps heps_half hf hx hnu
    (hz nu hnu).1 (hz nu hnu).2

/-- An interior frequency has an interior inverse point. -/
theorem inverse_mem_Ioo {a b : ℝ} {f x : ℝ → ℝ}
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    {nu : ℝ} (hnu : nu ∈ Ioo (deriv f b) (deriv f a)) :
    x nu ∈ Ioo a b := by
  have hnu_closed : nu ∈ Icc (deriv f b) (deriv f a) :=
    ⟨hnu.1.le, hnu.2.le⟩
  have hxnu := hx nu hnu_closed
  constructor
  · have hne : a ≠ x nu := by
      intro heq
      rw [← heq] at hxnu
      linarith [hnu.2]
    exact lt_of_le_of_ne hxnu.1.1 hne
  · have hne : x nu ≠ b := by
      intro heq
      rw [heq] at hxnu
      linarith [hnu.1]
    exact lt_of_le_of_ne hxnu.1.2 hne

/-! ### Smoothness of the inverse on the open derivative interval -/

/-- The inverse data in Lemma 3.9 are locally `C^(P-1)` at every interior
frequency.  The proof identifies the given inverse with Mathlib's local
inverse of `f'`; no global regularity of `x` is assumed. -/
theorem inverse_contDiffAt {N s y eps a b : ℝ} {P : ℕ} {f x : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) (hP : 2 ≤ P)
    (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) (_hab : a < b)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    {nu : ℝ} (hnu : nu ∈ Ioo (deriv f b) (deriv f a)) :
    ContDiffAt ℝ (P - 1) x nu := by
  let u : ℝ := x nu
  have hnu_closed : nu ∈ Icc (deriv f b) (deriv f a) :=
    ⟨hnu.1.le, hnu.2.le⟩
  have hu_eq : deriv f u = nu := (hx nu hnu_closed).2
  have hu : u ∈ Ioo a b :=
    inverse_mem_Ioo hx hnu
  have hP_one : 1 ≤ P := by omega
  have hP_pred_pos : 0 < P - 1 := by omega
  have hP_pred_ne : (((P - 1 : ℕ) : WithTop ℕ∞)) ≠ 0 := by
    exact_mod_cast hP_pred_pos.ne'
  have hfP : ContDiff ℝ ((P - 1 : ℕ) + 1) f := by
    exact hf.2.2.2.1.of_le (by
      exact_mod_cast (show P - 1 + 1 ≤ P by omega))
  have hg : ContDiff ℝ (P - 1) (deriv f) :=
    (contDiff_succ_iff_deriv.mp hfP).2.2
  have hgAt : ContDiffAt ℝ (P - 1) (deriv f) u := hg.contDiffAt
  have hsecond : deriv (deriv f) u < 0 :=
    deriv_deriv_neg_of_mem_Icc hN hs hy hP heps heps_half hf
      ⟨hu.1.le, hu.2.le⟩
  have hsecond_ne : deriv (deriv f) u ≠ 0 := hsecond.ne
  have hg_deriv : HasDerivAt (deriv f) (deriv (deriv f) u) u :=
    (hg.differentiable hP_pred_ne).differentiableAt.hasDerivAt
  have hg_equiv := hg_deriv.hasFDerivAt_equiv hsecond_ne
  let inv : ℝ → ℝ := hgAt.localInverse hg_equiv hP_pred_ne
  have hinv_cd : ContDiffAt ℝ (P - 1) inv nu := by
    simpa only [inv, hu_eq] using hgAt.to_localInverse hg_equiv hP_pred_ne
  have hinv_apply : inv nu = u := by
    simpa only [inv, hu_eq] using
      hgAt.localInverse_apply_image hg_equiv hP_pred_ne
  have hinv_right : ∀ᶠ v in nhds nu, deriv f (inv v) = v := by
    have hstrict := hgAt.hasStrictFDerivAt' hg_equiv hP_pred_ne
    simpa only [inv, ContDiffAt.localInverse, hu_eq] using
      hstrict.eventually_right_inverse
  have hinv_mem : ∀ᶠ v in nhds nu, inv v ∈ Ioo a b := by
    apply hinv_cd.continuousAt.eventually_mem
    rw [hinv_apply]
    exact Ioo_mem_nhds hu.1 hu.2
  have heq : x =ᶠ[nhds nu] inv := by
    filter_upwards [Ioo_mem_nhds hnu.1 hnu.2, hinv_mem, hinv_right] with v hv hInv hv_eq
    have hxv := hx v ⟨hv.1.le, hv.2.le⟩
    exact (deriv_strictAntiOn hN hs hy hP heps heps_half hf).injOn
      hxv.1 ⟨hInv.1.le, hInv.2.le⟩ (hxv.2.trans hv_eq.symm)
  exact hinv_cd.congr_of_eventuallyEq heq

/-! ### The Legendre identity -/

/-- Differentiating the Legendre identity gives `phi' = x` at every interior
frequency.  The differentiability of `x` is supplied by `inverse_contDiffAt`.
-/
theorem deriv_phi_eq_inverse {N s y eps a b : ℝ} {P : ℕ}
    {f x phi : ℝ → ℝ} (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) (hab : a < b)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hphi : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu))
    {nu : ℝ} (hnu : nu ∈ Ioo (deriv f b) (deriv f a)) :
    deriv phi nu = x nu := by
  have hP_pred_ne : (((P - 1 : ℕ) : WithTop ℕ∞)) ≠ 0 := by
    exact_mod_cast (by omega : P - 1 ≠ 0)
  have hx_cd : ContDiffAt ℝ (P - 1) x nu :=
    inverse_contDiffAt hN hs hy hP heps heps_half hf hab hx hnu
  have hx_deriv : HasDerivAt x (deriv x nu) nu :=
    (hx_cd.differentiableAt hP_pred_ne).hasDerivAt
  have hf_diff : Differentiable ℝ f :=
    (contDiff_two hP hf).differentiable (by norm_num)
  have hf_deriv : HasDerivAt f (deriv f (x nu)) (x nu) :=
    hf_diff.differentiableAt.hasDerivAt
  have hnu_eq : deriv f (x nu) = nu :=
    (hx nu ⟨hnu.1.le, hnu.2.le⟩).2
  have hrhs : HasDerivAt (fun v : ℝ => v * x v - f (x v)) (x nu) nu := by
    convert ((hasDerivAt_id nu).mul hx_deriv).sub
      (hf_deriv.comp nu hx_deriv) using 1
    all_goals try rfl
    rw [hnu_eq]
    simp only [id_eq]
    ring
  have hIoo : ∀ᶠ v in nhds nu,
      v ∈ Ioo (deriv f b) (deriv f a) :=
    Ioo_mem_nhds hnu.1 hnu.2
  have heq : phi =ᶠ[nhds nu] fun v : ℝ => v * x v - f (x v) :=
    hIoo.mono fun v hv =>
      hphi v ⟨hv.1.le, hv.2.le⟩
  exact (hrhs.congr_of_eventuallyEq heq).deriv

end GK39

end LeanProofs.IntegerPoints
