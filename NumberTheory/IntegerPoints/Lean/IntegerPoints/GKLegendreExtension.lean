import IntegerPoints.GKStatements
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Global Legendre data from negative curvature

Graham--Kolesnik's Lemma 3.9 is stated for an inverse `x` and a globally
`C^P` Legendre phase `phi`.  The hypotheses used later in the `B`-process,
however, initially give only a phase `f` whose second derivative is negative
on a compact interval.  This module supplies the missing existence bridge.

The construction deliberately does not assert that the inverse is globally
smooth.  We first enlarge the spatial interval slightly while preserving
negative curvature, and use `Function.invFunOn` for the inverse of `f'` on
that larger interval.  The inverse is locally `C^(P-1)` throughout the open
derivative interval by the inverse function theorem.  A smooth bump equal to
one on the original derivative interval and supported strictly inside the
larger one turns it into a globally `C^(P-1)` function.  Integrating that
localized inverse gains the final derivative and produces a globally `C^P`
Legendre phase.  On the original interval the fundamental theorem of calculus
identifies this primitive with `nu * x nu - f (x nu)`.
-/

open Filter Function Metric Set
open scoped Interval Topology

noncomputable section

namespace LeanProofs.IntegerPoints

namespace GKLegendre

/-! ### Enlarging a negative-curvature interval -/

/-- A globally `C^P` real function with `P >= 2` has continuous second
derivative. -/
theorem continuous_second_deriv {P : ℕ} {f : ℝ → ℝ} (hP : 2 ≤ P)
    (hf : ContDiff ℝ P f) : Continuous (deriv (deriv f)) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by exact_mod_cast hP)
  have hf1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) f from hf2)).2.2
  exact (contDiff_succ_iff_deriv.mp
    (show ContDiff ℝ (0 + 1) (deriv f) from hf1)).2.2.continuous

/-- Strict negativity of a continuous function on a nondegenerate compact
interval persists on a slightly larger closed interval. -/
theorem exists_interval_extension {a b : ℝ} {g : ℝ → ℝ} (hab : a < b)
    (hg : Continuous g) (hneg : ∀ t ∈ Icc a b, g t < 0) :
    ∃ a0 b0 : ℝ, a0 < a ∧ b < b0 ∧ ∀ t ∈ Icc a0 b0, g t < 0 := by
  let U : Set ℝ := {t | g t < 0}
  have hU : IsOpen U := isOpen_lt hg continuous_const
  have habU : Icc a b ⊆ U := by
    intro t ht
    exact hneg t ht
  obtain ⟨delta, hdelta, hthick⟩ :=
    isCompact_Icc.exists_cthickening_subset_open hU habU
  refine ⟨a - delta / 2, b + delta / 2, by linarith, by linarith, ?_⟩
  intro t ht
  apply hthick
  by_cases hta : t < a
  · apply mem_cthickening_of_dist_le t a delta (Icc a b)
      ⟨le_rfl, hab.le⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hta.le)]
    linarith [ht.1]
  by_cases htb : b < t
  · apply mem_cthickening_of_dist_le t b delta (Icc a b)
      ⟨hab.le, le_rfl⟩
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htb.le)]
    linarith [ht.2]
  exact self_subset_cthickening (δ := delta) (Icc a b)
    ⟨le_of_not_gt hta, le_of_not_gt htb⟩

/-! ### The inverse on a compact interval -/

/-- The set-theoretic inverse of `f'` restricted to a closed interval.  Its
values outside the image interval are intentionally unspecified. -/
noncomputable def inverseOn (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  Function.invFunOn (deriv f) (Icc a b)

/-- A continuous function with negative derivative is strictly decreasing on
the closed interval. -/
theorem strictAntiOn_of_second_deriv_neg {a b : ℝ} {f : ℝ → ℝ}
    (hderiv : Continuous (deriv f))
    (hneg : ∀ t ∈ Icc a b, deriv (deriv f) t < 0) :
    StrictAntiOn (deriv f) (Icc a b) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc a b) hderiv.continuousOn ?_
  intro t ht
  exact hneg t (interior_subset ht)

/-- The restricted inverse maps the reversed derivative interval back to the
spatial interval and is a right inverse there. -/
theorem inverseOn_spec {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hderiv : Continuous (deriv f))
    (hanti : StrictAntiOn (deriv f) (Icc a b)) :
    ∀ nu ∈ Icc (deriv f b) (deriv f a),
      inverseOn f a b nu ∈ Icc a b ∧ deriv f (inverseOn f a b nu) = nu := by
  have himage : deriv f '' Icc a b = Icc (deriv f b) (deriv f a) :=
    hderiv.continuousOn.image_Icc_of_antitoneOn hab hanti.antitoneOn
  intro nu hnu
  have hex : ∃ z ∈ Icc a b, deriv f z = nu := by
    rcases himage.symm.subset hnu with ⟨z, hz, hzeq⟩
    exact ⟨z, hz, hzeq⟩
  exact Function.invFunOn_pos hex

/-- Frequencies in the open derivative interval have inverse points in the
open spatial interval. -/
theorem inverseOn_mem_Ioo {a b : ℝ} {f : ℝ → ℝ} (hab : a < b)
    (hderiv : Continuous (deriv f))
    (hanti : StrictAntiOn (deriv f) (Icc a b)) {nu : ℝ}
    (hnu : nu ∈ Ioo (deriv f b) (deriv f a)) :
    inverseOn f a b nu ∈ Ioo a b := by
  have hnu' : nu ∈ Icc (deriv f b) (deriv f a) :=
    ⟨hnu.1.le, hnu.2.le⟩
  have hx := inverseOn_spec hab.le hderiv hanti nu hnu'
  constructor
  · have hne : a ≠ inverseOn f a b nu := by
      intro heq
      rw [← heq] at hx
      linarith [hnu.2]
    exact lt_of_le_of_ne hx.1.1 hne
  · have hne : inverseOn f a b nu ≠ b := by
      intro heq
      rw [heq] at hx
      linarith [hnu.1]
    exact lt_of_le_of_ne hx.1.2 hne

/-- The inverse of `f'` on `[a,b]` is locally `C^(P-1)` at every frequency
strictly between its endpoint derivatives. -/
theorem inverseOn_contDiffAt {P : ℕ} {a b : ℝ} {f : ℝ → ℝ}
    (hP : 2 ≤ P) (hab : a < b) (hf : ContDiff ℝ P f)
    (hneg : ∀ t ∈ Icc a b, deriv (deriv f) t < 0) {nu : ℝ}
    (hnu : nu ∈ Ioo (deriv f b) (deriv f a)) :
    ContDiffAt ℝ (P - 1 : ℕ) (inverseOn f a b) nu := by
  let u : ℝ := inverseOn f a b nu
  have hP_one : 1 ≤ P := by omega
  have hP_pred_pos : 0 < P - 1 := by omega
  have hP_pred_ne : (((P - 1 : ℕ) : WithTop ℕ∞)) ≠ 0 := by
    exact_mod_cast hP_pred_pos.ne'
  have hfP : ContDiff ℝ ((P - 1 : ℕ) + 1) f := by
    exact hf.of_le (by
      exact_mod_cast (show P - 1 + 1 ≤ P by omega))
  have hg : ContDiff ℝ (P - 1 : ℕ) (deriv f) :=
    (contDiff_succ_iff_deriv.mp hfP).2.2
  have hderiv : Continuous (deriv f) :=
    hf.continuous_deriv (by exact_mod_cast hP_one)
  have hanti : StrictAntiOn (deriv f) (Icc a b) :=
    strictAntiOn_of_second_deriv_neg hderiv hneg
  have hu : u ∈ Ioo a b :=
    inverseOn_mem_Ioo hab hderiv hanti hnu
  have hnu_closed : nu ∈ Icc (deriv f b) (deriv f a) :=
    ⟨hnu.1.le, hnu.2.le⟩
  have hu_eq : deriv f u = nu :=
    (inverseOn_spec hab.le hderiv hanti nu hnu_closed).2
  have hgAt : ContDiffAt ℝ (P - 1 : ℕ) (deriv f) u := hg.contDiffAt
  have hsecond : deriv (deriv f) u < 0 := hneg u ⟨hu.1.le, hu.2.le⟩
  have hsecond_ne : deriv (deriv f) u ≠ 0 := hsecond.ne
  have hg_deriv : HasDerivAt (deriv f) (deriv (deriv f) u) u :=
    (hg.differentiable hP_pred_ne).differentiableAt.hasDerivAt
  have hg_equiv := hg_deriv.hasFDerivAt_equiv hsecond_ne
  let inv : ℝ → ℝ := hgAt.localInverse hg_equiv hP_pred_ne
  have hinv_cd : ContDiffAt ℝ (P - 1 : ℕ) inv nu := by
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
  have heq : inverseOn f a b =ᶠ[nhds nu] inv := by
    filter_upwards [Ioo_mem_nhds hnu.1 hnu.2, hinv_mem, hinv_right] with v hv hInv hv_eq
    have hxv := inverseOn_spec hab.le hderiv hanti v ⟨hv.1.le, hv.2.le⟩
    exact hanti.injOn hxv.1 ⟨hInv.1.le, hInv.2.le⟩ (hxv.2.trans hv_eq.symm)
  exact hinv_cd.congr_of_eventuallyEq heq

/-- If a frequency lies in the derivative interval of a subinterval, the
inverse formed on a larger interval actually lies in that subinterval. -/
theorem inverseOn_spec_subinterval {a0 a b b0 : ℝ} {f : ℝ → ℝ}
    (ha0 : a0 ≤ a) (hab : a ≤ b) (hb0 : b ≤ b0)
    (hderiv : Continuous (deriv f))
    (hanti : StrictAntiOn (deriv f) (Icc a0 b0)) :
    ∀ nu ∈ Icc (deriv f b) (deriv f a),
      inverseOn f a0 b0 nu ∈ Icc a b ∧
        deriv f (inverseOn f a0 b0 nu) = nu := by
  intro nu hnu
  have ha0b : a0 ≤ b := ha0.trans hab
  have ha0b0 : a0 ≤ b0 := ha0b.trans hb0
  have hnu_outer : nu ∈ Icc (deriv f b0) (deriv f a0) := by
    constructor
    · exact (hanti.antitoneOn ⟨ha0b, hb0⟩
        ⟨ha0b0, le_rfl⟩ hb0).trans hnu.1
    · exact hnu.2.trans (hanti.antitoneOn
        ⟨le_rfl, ha0b0⟩ ⟨ha0, hab.trans hb0⟩ ha0)
  have hx := inverseOn_spec ha0b0 hderiv hanti nu hnu_outer
  refine ⟨⟨?_, ?_⟩, hx.2⟩
  · by_contra hxa
    have hlt : inverseOn f a0 b0 nu < a := lt_of_not_ge hxa
    have hstrict := hanti hx.1 ⟨ha0, hab.trans hb0⟩ hlt
    linarith [hnu.2]
  · by_contra hxb
    have hlt : b < inverseOn f a0 b0 nu := lt_of_not_ge hxb
    have hstrict := hanti ⟨ha0.trans hab, hb0⟩ hx.1 hlt
    linarith [hnu.1]

/-! ### Smoothly localizing the inverse -/

/-- A function that is locally `C^n` on an open interval can be multiplied
by a smooth cutoff to give a globally `C^n` function, while preserving it on
any smaller compact interval. -/
theorem exists_bumped_extension {n : ℕ} {alpha0 alpha beta beta0 : ℝ}
    {x : ℝ → ℝ} (halpha : alpha0 < alpha) (hab : alpha < beta)
    (hbeta : beta < beta0)
    (hx : ∀ nu ∈ Ioo alpha0 beta0, ContDiffAt ℝ n x nu) :
    ∃ xg : ℝ → ℝ, ContDiff ℝ n xg ∧ EqOn xg x (Icc alpha beta) := by
  let c : ℝ := (alpha + beta) / 2
  let rIn : ℝ := (beta - alpha) / 2
  let margin : ℝ := min (alpha - alpha0) (beta0 - beta)
  let rOut : ℝ := rIn + margin / 2
  have hrIn : 0 < rIn := by dsimp [rIn]; linarith
  have hmargin : 0 < margin := by
    dsimp [margin]
    exact lt_min (sub_pos.mpr halpha) (sub_pos.mpr hbeta)
  have hradii : rIn < rOut := by dsimp [rOut]; linarith
  let rho : ContDiffBump c :=
    { rIn := rIn
      rOut := rOut
      rIn_pos := hrIn
      rIn_lt_rOut := hradii }
  let xg : ℝ → ℝ := fun nu => rho nu * x nu
  have hsupp : tsupport (rho : ℝ → ℝ) ⊆ Ioo alpha0 beta0 := by
    intro nu hnu
    rw [rho.tsupport_eq, Real.closedBall_eq_Icc] at hnu
    change nu ∈ Icc (c - rOut) (c + rOut) at hnu
    have hmleft : margin ≤ alpha - alpha0 := min_le_left _ _
    have hmright : margin ≤ beta0 - beta := min_le_right _ _
    have hleft : c - rOut = alpha - margin / 2 := by
      dsimp [c, rOut, rIn]
      ring
    have hright : c + rOut = beta + margin / 2 := by
      dsimp [c, rOut, rIn]
      ring
    rw [hleft, hright] at hnu
    constructor
    · linarith [hnu.1, half_lt_self hmargin]
    · linarith [hnu.2, half_lt_self hmargin]
  have hxg : ContDiff ℝ n xg := by
    rw [contDiff_iff_contDiffAt]
    intro nu
    by_cases hnu : nu ∈ tsupport (rho : ℝ → ℝ)
    · exact rho.contDiffAt.mul (hx nu (hsupp hnu))
    · have hrho : (rho : ℝ → ℝ) =ᶠ[nhds nu] (fun _ => (0 : ℝ)) :=
        notMem_tsupport_iff_eventuallyEq.mp hnu
      have hzero : xg =ᶠ[nhds nu] (fun _ => 0) := by
        filter_upwards [hrho] with v hv
        change rho v = 0 at hv
        simp only [xg, hv, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  refine ⟨xg, hxg, ?_⟩
  intro nu hnu
  have hball : nu ∈ closedBall c rIn := by
    simpa only [c, rIn, Real.Icc_eq_closedBall] using hnu
  simp only [xg, rho.one_of_mem_closedBall hball, one_mul]

/-! ### A globally smooth primitive -/

/-- A primitive normalized to take the value `C` at `base`. -/
noncomputable def primitive (base C : ℝ) (g : ℝ → ℝ) (nu : ℝ) : ℝ :=
  C + ∫ u in base..nu, g u

/-- The derivative of the normalized primitive of a continuous function. -/
theorem primitive_hasDerivAt {base C nu : ℝ} {g : ℝ → ℝ}
    (hg : Continuous g) : HasDerivAt (primitive base C g) (g nu) nu := by
  exact (intervalIntegral.integral_hasDerivAt_right
    (hg.intervalIntegrable base nu)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter
    hg.continuousAt).const_add C

/-- Taking a primitive raises finite differentiability by one. -/
theorem primitive_contDiff {n : ℕ} {base C : ℝ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ n g) : ContDiff ℝ (n + 1) (primitive base C g) := by
  have hcont : Continuous g := hg.continuous
  have hdiff : Differentiable ℝ (primitive base C g) := fun nu =>
    (primitive_hasDerivAt (base := base) (C := C) (nu := nu) hcont).differentiableAt
  have hderiv : deriv (primitive base C g) = g := by
    funext nu
    exact (primitive_hasDerivAt (base := base) (C := C) (nu := nu) hcont).deriv
  refine contDiff_succ_iff_deriv.mpr ⟨hdiff, by simp, ?_⟩
  simpa only [hderiv] using hg

/-- Differentiating the Legendre expression cancels the derivative of the
inverse whenever `f' (x nu) = nu`. -/
theorem hasDerivAt_legendre {f x : ℝ → ℝ} {nu : ℝ}
    (hf : Differentiable ℝ f) (hx : DifferentiableAt ℝ x nu)
    (hinv : deriv f (x nu) = nu) :
    HasDerivAt (fun v => v * x v - f (x v)) (x nu) nu := by
  have hx' : HasDerivAt x (deriv x nu) nu := hx.hasDerivAt
  have hf' : HasDerivAt f (deriv f (x nu)) (x nu) :=
    hf.differentiableAt.hasDerivAt
  convert ((hasDerivAt_id nu).mul hx').sub (hf'.comp nu hx') using 1
  all_goals try rfl
  rw [hinv]
  simp only [id_eq]
  ring

/-! ### The global existence bridge -/

/-- Negative curvature on a nondegenerate interval supplies all globally
quantified Legendre data required by Graham--Kolesnik Lemma 3.9.

The inverse `x` is globally defined but is only asserted to have the inverse
property on the displayed derivative interval.  The Legendre phase `phi` is
globally `C^P`, exactly as required by `gk_lemma39`. -/
theorem exists_legendre_data {P : ℕ} {a b : ℝ} {f : ℝ → ℝ}
    (hP : 2 ≤ P) (hab : a < b) (hf : ContDiff ℝ P f)
    (hneg : ∀ t ∈ Icc a b, deriv (deriv f) t < 0) :
    ∃ x phi : ℝ → ℝ,
      ContDiff ℝ P phi ∧
      (∀ nu ∈ Icc (deriv f b) (deriv f a),
        x nu ∈ Icc a b ∧ deriv f (x nu) = nu) ∧
      (∀ nu ∈ Icc (deriv f b) (deriv f a),
        phi nu = nu * x nu - f (x nu)) := by
  have hsecond : Continuous (deriv (deriv f)) :=
    continuous_second_deriv hP hf
  obtain ⟨a0, b0, ha0, hb0, hneg0⟩ :=
    exists_interval_extension hab hsecond hneg
  have hab0 : a0 < b0 := ha0.trans (hab.trans hb0)
  have hderiv : Continuous (deriv f) :=
    hf.continuous_deriv (by exact_mod_cast (show 1 ≤ P by omega))
  have hanti0 : StrictAntiOn (deriv f) (Icc a0 b0) :=
    strictAntiOn_of_second_deriv_neg hderiv hneg0
  have halpha : deriv f b0 < deriv f b :=
    hanti0 ⟨ha0.le.trans hab.le, hb0.le⟩ ⟨hab0.le, le_rfl⟩ hb0
  have hmiddle : deriv f b < deriv f a :=
    hanti0 ⟨ha0.le, hab.le.trans hb0.le⟩
      ⟨ha0.le.trans hab.le, hb0.le⟩ hab
  have hbeta : deriv f a < deriv f a0 :=
    hanti0 ⟨le_rfl, hab0.le⟩ ⟨ha0.le, hab.le.trans hb0.le⟩ ha0
  let x : ℝ → ℝ := inverseOn f a0 b0
  have hxlocal : ∀ nu ∈ Ioo (deriv f b0) (deriv f a0),
      ContDiffAt ℝ (P - 1 : ℕ) x nu := by
    intro nu hnu
    exact inverseOn_contDiffAt hP hab0 hf hneg0 hnu
  obtain ⟨xg, hxg_cd, hxg_eq⟩ := exists_bumped_extension
    halpha hmiddle hbeta hxlocal
  let alpha : ℝ := deriv f b
  let C : ℝ := alpha * b - f b
  let phi : ℝ → ℝ := primitive alpha C xg
  have hphi_cd : ContDiff ℝ P phi := by
    have hp := primitive_contDiff (base := alpha) (C := C) hxg_cd
    exact hp.of_le (by
      exact_mod_cast (show P ≤ P - 1 + 1 by omega))
  have hx_spec : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu := by
    intro nu hnu
    exact inverseOn_spec_subinterval ha0.le hab.le hb0.le hderiv hanti0 nu hnu
  have hx_alpha : x alpha = b := by
    have hx := hx_spec alpha ⟨le_rfl, hmiddle.le⟩
    exact hanti0.injOn
      ⟨ha0.le.trans hx.1.1, hx.1.2.trans hb0.le⟩
      ⟨ha0.le.trans hab.le, hb0.le⟩
      (by simpa only [alpha] using hx.2)
  refine ⟨x, phi, hphi_cd, hx_spec, ?_⟩
  intro nu hnu
  have halpha_nu : alpha ≤ nu := hnu.1
  have hnu_beta : nu ≤ deriv f a := hnu.2
  have hsegment : Icc alpha nu ⊆ Icc (deriv f b) (deriv f a) := by
    intro v hv
    exact ⟨hv.1, hv.2.trans hnu_beta⟩
  have hxg_segment : EqOn xg x (Icc alpha nu) := by
    intro v hv
    exact hxg_eq (hsegment hv)
  let L : ℝ → ℝ := fun v => v * x v - f (x v)
  have hL_cd : ContDiffOn ℝ 1 L (Icc alpha nu) := by
    intro v hv
    have hv_orig := hsegment hv
    have hv_outer : v ∈ Ioo (deriv f b0) (deriv f a0) :=
      ⟨halpha.trans_le hv_orig.1, hv_orig.2.trans_lt hbeta⟩
    have hxv : ContDiffAt ℝ 1 x v :=
      (hxlocal v hv_outer).of_le (by exact_mod_cast (show 1 ≤ P - 1 by omega))
    have hfv : ContDiffAt ℝ 1 (fun w => f (x w)) v :=
      (hf.of_le (by exact_mod_cast (show 1 ≤ P by omega))).contDiffAt.comp v hxv
    exact ((contDiffAt_id.mul hxv).sub hfv).contDiffWithinAt
  have hderivL : ∀ v ∈ Icc alpha nu, deriv L v = x v := by
    intro v hv
    have hv_orig := hsegment hv
    have hv_outer : v ∈ Ioo (deriv f b0) (deriv f a0) :=
      ⟨halpha.trans_le hv_orig.1, hv_orig.2.trans_lt hbeta⟩
    have hxv : DifferentiableAt ℝ x v :=
      ((hxlocal v hv_outer).of_le
        (by exact_mod_cast (show 1 ≤ P - 1 by omega))).differentiableAt one_ne_zero
    have hf_diff : Differentiable ℝ f :=
      hf.differentiable (by exact_mod_cast (show P ≠ 0 by omega))
    exact (hasDerivAt_legendre hf_diff hxv (hx_spec v hv_orig).2).deriv
  have hint_xg : (∫ v in alpha..nu, xg v) = ∫ v in alpha..nu, x v :=
    intervalIntegral.integral_congr (by
      simpa only [uIcc_of_le halpha_nu] using hxg_segment)
  have hint_x : (∫ v in alpha..nu, x v) = L nu - L alpha := by
    rw [← intervalIntegral.integral_deriv_of_contDiffOn_Icc hL_cd halpha_nu]
    apply intervalIntegral.integral_congr
    intro v hv
    exact (hderivL v (by simpa only [uIcc_of_le halpha_nu] using hv)).symm
  calc
    phi nu = C + ∫ v in alpha..nu, xg v := rfl
    _ = C + ∫ v in alpha..nu, x v := by rw [hint_xg]
    _ = C + (L nu - L alpha) := by rw [hint_x]
    _ = L nu := by simp only [C, L, hx_alpha, alpha]; ring
    _ = nu * x nu - f (x nu) := rfl

end GKLegendre

end LeanProofs.IntegerPoints
