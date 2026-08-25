import IntegerPoints.IwaniecMozzochiEq124Eq117Bridge
import IntegerPoints.IwaniecMozzochiDyadicPartition
import IntegerPoints.IwaniecMozzochiSmoothWeight
import IntegerPoints.Lemma9Tools
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Iwaniec--Mozzochi (11.7): dimensionless cutoff regularity

The regularity interface used by the Section 12 specialization of (11.7)
initially quantifies six positive scale parameters.  Only one dimensionless
combination of five of them matters.  Put

```text
  r = ell / (2 * gamma * c * N * H),   t = xi / H.
```

Then the translated Bessel weight is exactly

```text
  chi(t) * rho(r / t - s).
```

This module isolates that normalization.  The support conditions
`supp chi subset [1,4]`, `supp rho subset [4,5]`, and `s in [0,3]` imply that
the normalized weight is identically zero for `r > 32`.  Derivatives also
vanish off `[1,4]`.  Consequently the original six-parameter regularity
condition is equivalent to bounding the second and third derivatives on the
compact dimensionless box

```text
  0 <= s <= 3,   0 < r <= 32,   1 <= t <= 4.
```

The remaining normalized jet estimate is elementary cutoff calculus, not an
oscillatory-integral or number-theoretic estimate.  To prove it uniformly, we
replace the denominator `t` by the existing globally positive smooth function
`L9.hfun`.  On the support of `chi` this replacement is exactly `t`.  The
second and third `t`-derivatives are therefore restrictions of jointly smooth
functions of `(s,r,t)`, so compactness of the displayed box supplies a common
bound.  Thus no analytic premise remains in the regularity interface.
-/

open Filter Set
open scoped ContDiff

namespace LeanProofs.IntegerPoints

noncomputable section

/-- The dimensionless form of the translated Section 12 Bessel weight. -/
def section12NormalizedBesselWeight
    (chi rho : Real → Real) (s r t : Real) : Real :=
  chi t * rho (r / t - s)

/-- The sole dimensionless ratio in the specialized Bessel weight. -/
def section12BesselRatio
    (gamma c H N ell : Real) : Real :=
  ell / (2 * gamma * c * N * H)

/-- Exact normalization of the translated Bessel weight. -/
theorem section12BesselWeight_eq_normalized
    (chi rho : Real → Real) (s gamma c H N ell xi : Real)
    (hgamma : gamma ≠ 0) (hc : c ≠ 0) (hH : H ≠ 0) (hN : N ≠ 0) :
    section12BesselWeight chi (fun u => rho (u - s))
        gamma c H N ell xi =
      section12NormalizedBesselWeight chi rho s
        (section12BesselRatio gamma c H N ell) (xi / H) := by
  unfold section12BesselWeight section12NormalizedBesselWeight
    section12BesselRatio
  have harg :
      ell / (2 * gamma * c * N * xi) =
        (ell / (2 * gamma * c * N * H)) / (xi / H) := by
    by_cases hxi : xi = 0
    · simp [hxi]
    · field_simp [hgamma, hc, hH, hN, hxi]
  rw [harg]

/-- Positive dilation preserves smooth compact support inside `(0,infinity)`.
This is the support counterpart of the derivative scaling used below. -/
theorem isSmoothCompactPos_div
    {f : Real → Real} (hf : IsSmoothCompactPos f)
    {H : Real} (hH : 0 < H) :
    IsSmoothCompactPos (fun x => f (x / H)) := by
  refine ⟨hf.1.comp (contDiff_id.div_const H), ?_, ?_⟩
  · have hcompact : HasCompactSupport (fun x : Real => f (H⁻¹ • x)) :=
      hf.2.1.comp_smul (inv_ne_zero hH.ne')
    simpa only [smul_eq_mul, inv_mul_eq_div] using hcompact
  · let e : Real ≃ₜ Real :=
      Homeomorph.smulOfNeZero H⁻¹ (inv_ne_zero hH.ne')
    intro x hx
    have heq : f ∘ e = fun y : Real => f (y / H) := by
      funext y
      change f (H⁻¹ • y) = f (y / H)
      rw [smul_eq_mul, inv_mul_eq_div]
    have hxComp : x ∈ tsupport (f ∘ e) := by
      rw [heq]
      exact hx
    have hx' : e x ∈ tsupport f :=
      (Set.ext_iff.mp (tsupport_comp_eq_preimage f e) x).mp hxComp
    have hscaled : 0 < H⁻¹ * x := by
      have := hf.2.2 hx'
      change 0 < H⁻¹ • x at this
      simpa only [smul_eq_mul] using this
    exact pos_of_mul_pos_right hscaled (inv_nonneg.mpr hH.le)

/-- Exact derivative scaling under `x mapsto x/H`. -/
theorem iteratedDeriv_comp_div
    {f : Real → Real} (hf : ContDiff Real ∞ f)
    {H x : Real} (j : Nat) :
    iteratedDeriv j (fun u : Real => f (u / H)) x =
      H⁻¹ ^ j * iteratedDeriv j f (x / H) := by
  have hcomp := iteratedDeriv_comp_const_mul (n := j)
    (contDiff_infty.mp hf j) H⁻¹
  simpa only [inv_mul_eq_div] using congrFun hcomp x

/-- Natural inverse powers agree with the real-power notation in (11.6). -/
theorem section12_inv_pow_eq_rpow {H : Real} (hH : 0 < H) (j : Nat) :
    H⁻¹ ^ j = H ^ (-(j : Real)) := by
  rw [Real.rpow_neg hH.le, Real.rpow_natCast, inv_pow]

/-- Every normalized translated cutoff is smooth, compactly supported, and
supported in the positive half-line.  The only apparent singularity is at
`t = 0`; there `chi` vanishes on a whole neighborhood. -/
theorem section12NormalizedBesselWeight_isSmoothCompactPos
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5) (s r : Real) :
    IsSmoothCompactPos (section12NormalizedBesselWeight chi rho s r) := by
  have hsmooth :
      ContDiff Real ∞ (section12NormalizedBesselWeight chi rho s r) := by
    rw [contDiff_iff_contDiffAt]
    intro t
    by_cases ht : t = 0
    · subst t
      have heq :
          section12NormalizedBesselWeight chi rho s r =ᶠ[nhds (0 : Real)]
            (fun _ : Real => 0) := by
        filter_upwards [Iio_mem_nhds (show (0 : Real) < 1 by norm_num)] with u hu
        unfold section12NormalizedBesselWeight
        rw [hchi.2.2.2.2 u hu.le, zero_mul]
      exact (contDiffAt_const (c := (0 : Real))).congr_of_eventuallyEq heq
    · have hquot : ContDiffAt Real ∞ (fun u : Real => r / u) t :=
        ContDiffAt.div contDiffAt_const contDiffAt_id ht
      have hinner : ContDiffAt Real ∞ (fun u : Real => r / u - s) t :=
        hquot.sub contDiffAt_const
      unfold section12NormalizedBesselWeight
      exact hchi.1.contDiffAt.mul (hrho.1.contDiffAt.comp t hinner)
  have hchiSupport : Function.support chi ⊆ Set.Icc (1 : Real) 4 := by
    intro t ht
    constructor
    · apply le_of_not_gt
      intro htOne
      exact ht (hchi.2.2.2.2 t htOne.le)
    · apply le_of_not_gt
      intro htFour
      exact ht (hchi.2.1 t htFour.le)
  have hchiCompact : HasCompactSupport chi :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hchiSupport
  have hcompact :
      HasCompactSupport (section12NormalizedBesselWeight chi rho s r) := by
    unfold section12NormalizedBesselWeight
    exact hchiCompact.mul_right
  have hchiTsupport : tsupport chi ⊆ Set.Icc (1 : Real) 4 :=
    closure_minimal hchiSupport isClosed_Icc
  have hpositive :
      tsupport (section12NormalizedBesselWeight chi rho s r) ⊆ Set.Ioi 0 := by
    intro t ht
    have htChi : t ∈ tsupport chi := by
      exact (tsupport_mul_subset_left
        (f := chi) (g := fun u : Real => rho (r / u - s))) ht
    exact lt_of_lt_of_le (by norm_num : (0 : Real) < 1)
      (hchiTsupport htChi).1
  exact ⟨hsmooth, hcompact, hpositive⟩

/-- The support overlap is empty once the dimensionless ratio exceeds `32`.
The constant is exactly `4 * (5 + 3)`, from the two support intervals and
the translation range. -/
theorem section12NormalizedBesselWeight_eq_zero_of_largeRatio
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5)
    {s r : Real} (hsThree : s ≤ 3) (hr : 32 < r) :
    section12NormalizedBesselWeight chi rho s r = 0 := by
  funext t
  unfold section12NormalizedBesselWeight
  by_cases hchiZero : chi t = 0
  · simp [hchiZero]
  · have htOne : 1 < t := by
      by_contra hnot
      exact hchiZero (hchi.2.2.2.2 t (le_of_not_gt hnot))
    have htFour : t < 4 := by
      by_contra hnot
      exact hchiZero (hchi.2.1 t (le_of_not_gt hnot))
    have hrhoZero : rho (r / t - s) = 0 := by
      by_contra hrhoNe
      have hsupp := hrho.2.2 (r / t - s) hrhoNe
      have hratio : r / t ≤ 8 := by linarith [hsupp.2]
      have hrLe : r ≤ 8 * t := (div_le_iff₀ (by linarith : 0 < t)).mp hratio
      linarith
    simp [hrhoZero]

/-- The compact, dimensionless jet estimate left after exact normalization.
It involves no oscillatory integral and no Section 12 scale parameter. -/
def Section12NormalizedJetBoundFor (chi rho : Real → Real) : Prop :=
  ∃ D : Real, 0 < D ∧
    ∀ s r t : Real,
      0 ≤ s → s ≤ 3 → 0 < r → r ≤ 32 →
      t ∈ Set.Icc (1 : Real) 4 →
        |iteratedDeriv 2 (section12NormalizedBesselWeight chi rho s r) t| ≤ D ∧
        |iteratedDeriv 3 (section12NormalizedBesselWeight chi rho s r) t| ≤ D

/-! ## Joint smooth-cutoff calculus on the normalized box -/

/-- The joint parameter space `(s,r,t)` for the normalized cutoff. -/
private abbrev Section12NormalizedPoint := (Real × Real) × Real

/-- The direction which differentiates only the normalized integration
variable `t`. -/
private def section12NormalizedTimeDirection : Section12NormalizedPoint :=
  ((0, 0), 1)

/-- `L9.hfun` is the globally positive smooth replacement for `t`. -/
private theorem section12SmoothRadius_contDiff :
    ContDiff Real ∞ L9.hfun := by
  rw [contDiff_infty]
  exact L9.hfun_contDiff_nat

/-- A globally smooth joint representative of the normalized weight.  It is
equal to the literal weight wherever `chi` can be nonzero. -/
private noncomputable def section12SafeNormalizedWeight
    (chi rho : Real → Real) (z : Section12NormalizedPoint) : Real :=
  chi z.2 * rho (z.1.2 / L9.hfun z.2 - z.1.1)

private theorem section12SafeNormalizedWeight_contDiff
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5) :
    ContDiff Real ∞ (section12SafeNormalizedWeight chi rho) := by
  have hchiSmooth : ContDiff Real ∞ chi := by simpa only using hchi.1
  have hrhoSmooth : ContDiff Real ∞ rho := by simpa only using hrho.1
  have hfunSmooth : ContDiff Real ∞ L9.hfun :=
    section12SmoothRadius_contDiff
  have hquot : ContDiff Real ∞ (fun z : Section12NormalizedPoint =>
      z.1.2 / L9.hfun z.2) :=
    (by fun_prop : ContDiff Real ∞ (fun z : Section12NormalizedPoint => z.1.2)).div
      (hfunSmooth.comp (by fun_prop))
      (fun z => (L9.hfun_pos z.2).ne')
  have hinner : ContDiff Real ∞ (fun z : Section12NormalizedPoint =>
      z.1.2 / L9.hfun z.2 - z.1.1) :=
    hquot.sub (by fun_prop)
  have hchiComp : ContDiff Real ∞ (fun z : Section12NormalizedPoint => chi z.2) :=
    hchiSmooth.comp (by fun_prop)
  have hrhoComp : ContDiff Real ∞ (fun z : Section12NormalizedPoint =>
      rho (z.1.2 / L9.hfun z.2 - z.1.1)) :=
    hrhoSmooth.comp hinner
  unfold section12SafeNormalizedWeight
  exact hchiComp.mul hrhoComp

private theorem section12SafeNormalizedWeight_eq_normalized
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (s r : Real) :
    (fun t : Real => section12SafeNormalizedWeight chi rho ((s, r), t)) =
      section12NormalizedBesselWeight chi rho s r := by
  funext t
  unfold section12SafeNormalizedWeight section12NormalizedBesselWeight
  by_cases hchiZero : chi t = 0
  · simp only [hchiZero, zero_mul]
  · have htOne : 1 < t := by
      apply lt_of_not_ge
      intro ht
      exact hchiZero (hchi.2.2.2.2 t ht)
    rw [L9.hfun_eq (by linarith : (1 / 2 : Real) ≤ t)]

/-- Jointly smooth directional derivatives in the `t` coordinate.  Defining
the jets in the full `(s,r,t)` space is what makes compactness uniform in the
translation and ratio parameters. -/
private noncomputable def section12NormalizedJet
    (chi rho : Real → Real) : Nat → Section12NormalizedPoint → Real
  | 0 => section12SafeNormalizedWeight chi rho
  | n + 1 => fun z =>
      fderiv Real (section12NormalizedJet chi rho n) z
        section12NormalizedTimeDirection

private theorem section12NormalizedJet_contDiff
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5) (n : Nat) :
    ContDiff Real ∞ (section12NormalizedJet chi rho n) := by
  induction n with
  | zero =>
      simpa only [section12NormalizedJet] using
        section12SafeNormalizedWeight_contDiff hchi hrho
  | succ n ih =>
      have hFD : ContDiff Real ∞
          (fderiv Real (section12NormalizedJet chi rho n)) :=
        ih.fderiv_right (by simp)
      have happly : ContDiff Real ∞ (fun z =>
          fderiv Real (section12NormalizedJet chi rho n) z
            section12NormalizedTimeDirection) :=
        hFD.clm_apply contDiff_const
      simpa only [section12NormalizedJet] using happly

/-- Restricting the joint directional jet to fixed `(s,r)` gives the ordinary
one-variable iterated derivative. -/
private theorem iteratedDeriv_section12SafeNormalizedWeight
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5) (n : Nat) (s r t : Real) :
    iteratedDeriv n
        (fun u : Real => section12SafeNormalizedWeight chi rho ((s, r), u)) t =
      section12NormalizedJet chi rho n ((s, r), t) := by
  induction n generalizing t with
  | zero => simp only [iteratedDeriv_zero, section12NormalizedJet]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq :
          iteratedDeriv n
              (fun u : Real => section12SafeNormalizedWeight chi rho ((s, r), u)) =
            fun u : Real => section12NormalizedJet chi rho n ((s, r), u) := by
        funext u
        exact ih u
      rw [heq]
      have hinsert : HasDerivAt (fun u : Real => ((s, r), u))
          ((0, 0), 1) t :=
        (hasDerivAt_const t (s, r)).prodMk (hasDerivAt_id t)
      have hcomp :=
        ((section12NormalizedJet_contDiff hchi hrho n).differentiable (by simp))
          |>.differentiableAt.hasFDerivAt.comp_hasDerivAt t hinsert
      have hderiv : HasDerivAt
          (fun u : Real => section12NormalizedJet chi rho n ((s, r), u))
          (fderiv Real (section12NormalizedJet chi rho n) ((s, r), t)
            section12NormalizedTimeDirection) t := by
        simpa only [Function.comp_def, section12NormalizedTimeDirection]
          using hcomp
      simpa only [section12NormalizedJet] using hderiv.deriv

/-- The literal normalized derivatives are the jointly smooth jets. -/
private theorem iteratedDeriv_section12NormalizedBesselWeight
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5) (n : Nat) (s r t : Real) :
    iteratedDeriv n (section12NormalizedBesselWeight chi rho s r) t =
      section12NormalizedJet chi rho n ((s, r), t) := by
  rw [← section12SafeNormalizedWeight_eq_normalized hchi s r]
  exact iteratedDeriv_section12SafeNormalizedWeight hchi hrho n s r t

/-- The one fixed compact box containing every potentially nonzero normalized
jet under the Section 12 translation hypotheses. -/
private def section12NormalizedJetBox : Set Section12NormalizedPoint :=
  (Icc (0 : Real) 3 ×ˢ Icc (0 : Real) 32) ×ˢ Icc (1 : Real) 4

private theorem section12NormalizedJetBox_isCompact :
    IsCompact section12NormalizedJetBox :=
  (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

private theorem section12NormalizedJetBox_nonempty :
    section12NormalizedJetBox.Nonempty := by
  refine ⟨((0, 0), 1), ?_⟩
  norm_num [section12NormalizedJetBox]

private theorem exists_section12NormalizedJet_bound
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5) (n : Nat) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ z : Section12NormalizedPoint, z ∈ section12NormalizedJetBox →
        ‖section12NormalizedJet chi rho n z‖ ≤ C := by
  have hcontinuous : Continuous (fun z =>
      ‖section12NormalizedJet chi rho n z‖) :=
    (section12NormalizedJet_contDiff hchi hrho n).continuous.norm
  obtain ⟨z, hz, hmax⟩ :=
    section12NormalizedJetBox_isCompact.exists_isMaxOn
      section12NormalizedJetBox_nonempty hcontinuous.continuousOn
  exact ⟨‖section12NormalizedJet chi rho n z‖, norm_nonneg _,
    fun w hw => hmax hw⟩

/-- Smoothness and compactness prove the normalized jet estimate for every
admissible pair of cutoffs. -/
theorem section12NormalizedJetBoundFor_of_cutoffs
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5) :
    Section12NormalizedJetBoundFor chi rho := by
  obtain ⟨Ctwo, hCtwo, htwo⟩ :=
    exists_section12NormalizedJet_bound hchi hrho 2
  obtain ⟨Cthree, hCthree, hthree⟩ :=
    exists_section12NormalizedJet_bound hchi hrho 3
  refine ⟨1 + Ctwo + Cthree, by linarith, ?_⟩
  intro s r t hsZero hsThree hr hrUpper ht
  have hz : ((s, r), t) ∈ section12NormalizedJetBox :=
    ⟨⟨⟨hsZero, hsThree⟩, ⟨hr.le, hrUpper⟩⟩, ht⟩
  rw [iteratedDeriv_section12NormalizedBesselWeight hchi hrho 2 s r t,
    iteratedDeriv_section12NormalizedBesselWeight hchi hrho 3 s r t]
  constructor
  · simpa only [Real.norm_eq_abs] using
      (htwo ((s, r), t) hz).trans
        (show Ctwo ≤ 1 + Ctwo + Cthree by linarith)
  · simpa only [Real.norm_eq_abs] using
      (hthree ((s, r), t) hz).trans
        (show Cthree ≤ 1 + Ctwo + Cthree by linarith)

/-- A compact-box jet estimate extends globally because `chi` and all its
jets vanish off `[1,4]`. -/
theorem section12NormalizedJetBound_global
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    {D s r : Real}
    (hbound : ∀ t ∈ Set.Icc (1 : Real) 4,
      |iteratedDeriv 2 (section12NormalizedBesselWeight chi rho s r) t| ≤ D ∧
      |iteratedDeriv 3 (section12NormalizedBesselWeight chi rho s r) t| ≤ D)
    (hD : 0 ≤ D) :
    ∀ t : Real,
      |iteratedDeriv 2 (section12NormalizedBesselWeight chi rho s r) t| ≤ D ∧
      |iteratedDeriv 3 (section12NormalizedBesselWeight chi rho s r) t| ≤ D := by
  intro t
  by_cases ht : t ∈ Set.Icc (1 : Real) 4
  · exact hbound t ht
  · have heq :
        section12NormalizedBesselWeight chi rho s r =ᶠ[nhds t]
          (fun _ : Real => 0) := by
      by_cases htLow : t < 1
      · filter_upwards [Iio_mem_nhds htLow] with u hu
        unfold section12NormalizedBesselWeight
        rw [hchi.2.2.2.2 u hu.le, zero_mul]
      · have htOne : (1 : Real) ≤ t := le_of_not_gt htLow
        have htHigh : 4 < t := by
          exact lt_of_not_ge (fun htFour => ht ⟨htOne, htFour⟩)
        filter_upwards [Ioi_mem_nhds htHigh] with u hu
        unfold section12NormalizedBesselWeight
        rw [hchi.2.1 u hu.le, zero_mul]
    have htwo :
        iteratedDeriv 2 (section12NormalizedBesselWeight chi rho s r) t = 0 := by
      simpa using Filter.EventuallyEq.iteratedDeriv_eq 2 heq
    have hthree :
        iteratedDeriv 3 (section12NormalizedBesselWeight chi rho s r) t = 0 := by
      simpa using Filter.EventuallyEq.iteratedDeriv_eq 3 heq
    simp only [htwo, hthree, abs_zero, hD, and_self]

/-- The compact normalized jet bound supplies the original six-parameter
regularity interface. -/
theorem section12Eq117RegularityFor_of_normalizedJetBound
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5)
    (hjets : Section12NormalizedJetBoundFor chi rho) :
    Section12Eq117RegularityFor chi rho := by
  obtain ⟨D, hD, hjets⟩ := hjets
  refine ⟨D, hD, ?_⟩
  intro s gamma c H N ell hsZero hsThree hgamma hc hH hN hell
  let r : Real := section12BesselRatio gamma c H N ell
  have hr : 0 < r := by
    unfold r section12BesselRatio
    positivity
  have hweightEq :
      section12BesselWeight chi (fun u => rho (u - s)) gamma c H N ell =
        fun xi => section12NormalizedBesselWeight chi rho s r (xi / H) := by
    funext xi
    exact section12BesselWeight_eq_normalized chi rho s gamma c H N ell xi
      hgamma.ne' hc.ne' hH.ne' hN.ne'
  by_cases hrUpper : r ≤ 32
  · have hnormalized :=
      section12NormalizedBesselWeight_isSmoothCompactPos hchi hrho s r
    have hlocal : ∀ t ∈ Set.Icc (1 : Real) 4,
        |iteratedDeriv 2 (section12NormalizedBesselWeight chi rho s r) t| ≤ D ∧
        |iteratedDeriv 3 (section12NormalizedBesselWeight chi rho s r) t| ≤ D :=
      fun t ht => hjets s r t hsZero hsThree hr hrUpper ht
    have hglobal := section12NormalizedJetBound_global hchi hlocal hD.le
    refine ⟨?_, ?_, ?_⟩
    · rw [hweightEq]
      exact isSmoothCompactPos_div hnormalized hH
    · intro xi
      rw [hweightEq, iteratedDeriv_comp_div hnormalized.1 2]
      rw [section12_inv_pow_eq_rpow hH 2, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hH.le _)]
      calc
        H ^ (-(2 : Real)) *
            |iteratedDeriv 2 (section12NormalizedBesselWeight chi rho s r)
              (xi / H)| ≤
            H ^ (-(2 : Real)) * D :=
          mul_le_mul_of_nonneg_left (hglobal (xi / H)).1
            (Real.rpow_nonneg hH.le _)
        _ = D * H ^ (-(2 : Real)) := by ring
    · intro xi
      rw [hweightEq, iteratedDeriv_comp_div hnormalized.1 3]
      rw [section12_inv_pow_eq_rpow hH 3, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hH.le _)]
      calc
        H ^ (-(3 : Real)) *
            |iteratedDeriv 3 (section12NormalizedBesselWeight chi rho s r)
              (xi / H)| ≤
            H ^ (-(3 : Real)) * D :=
          mul_le_mul_of_nonneg_left (hglobal (xi / H)).2
            (Real.rpow_nonneg hH.le _)
        _ = D * H ^ (-(3 : Real)) := by ring
  · have hrLarge : 32 < r := lt_of_not_ge hrUpper
    have hnormalizedZero :
        section12NormalizedBesselWeight chi rho s r = 0 :=
      section12NormalizedBesselWeight_eq_zero_of_largeRatio hchi hrho
        hsThree hrLarge
    have hweightZero :
        section12BesselWeight chi (fun u => rho (u - s)) gamma c H N ell = 0 := by
      funext xi
      calc
        section12BesselWeight chi (fun u => rho (u - s))
            gamma c H N ell xi =
            section12NormalizedBesselWeight chi rho s r (xi / H) :=
          congrFun hweightEq xi
        _ = 0 := by
          simpa only [Pi.zero_apply] using
            congrFun hnormalizedZero (xi / H)
    refine ⟨?_, ?_, ?_⟩
    · rw [hweightZero]
      exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
    · intro xi
      rw [hweightZero]
      simp only [iteratedDeriv_const_zero, abs_zero]
      exact mul_nonneg hD.le (Real.rpow_nonneg hH.le _)
    · intro xi
      rw [hweightZero]
      simp only [iteratedDeriv_const_zero, abs_zero]
      exact mul_nonneg hD.le (Real.rpow_nonneg hH.le _)

/-- Conversely, the original regularity interface contains the compact-box
jet bound as its unit-scale specialization. -/
theorem section12NormalizedJetBoundFor_of_regular
    {chi rho : Real → Real}
    (hregularity : Section12Eq117RegularityFor chi rho) :
    Section12NormalizedJetBoundFor chi rho := by
  obtain ⟨D, hD, hregularity⟩ := hregularity
  refine ⟨D, hD, ?_⟩
  intro s r t hsZero hsThree hr _hrUpper ht
  have hdata := hregularity s (1 / 2 : Real) 1 1 1 r
    hsZero hsThree (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hr
  have hweightEq :
      section12BesselWeight chi (fun u => rho (u - s)) (1 / 2 : Real) 1 1 1 r =
        section12NormalizedBesselWeight chi rho s r := by
    funext xi
    have hnormalized := section12BesselWeight_eq_normalized
      chi rho s (1 / 2 : Real) 1 1 1 r xi
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa [section12BesselRatio] using hnormalized
  rw [hweightEq] at hdata
  constructor
  · simpa using hdata.2.1 t
  · simpa using hdata.2.2 t

/-- Under the actual support hypotheses, the original regularity interface is
equivalent to the compact dimensionless jet problem. -/
theorem section12Eq117RegularityFor_iff_normalizedJetBound
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5) :
    Section12Eq117RegularityFor chi rho ↔
      Section12NormalizedJetBoundFor chi rho :=
  ⟨section12NormalizedJetBoundFor_of_regular,
    section12Eq117RegularityFor_of_normalizedJetBound hchi hrho⟩

/-- The Section 12 cutoff regularity interface is automatic for every dyadic
partition and every smooth weight supported in `[4,5]`. -/
theorem section12Eq117RegularityFor_of_cutoffs
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5) :
    Section12Eq117RegularityFor chi rho :=
  section12Eq117RegularityFor_of_normalizedJetBound hchi hrho
    (section12NormalizedJetBoundFor_of_cutoffs hchi hrho)

/-- Consequently the completed (11.7) theorem supplies its uniform
translation-specialized Section 12 stationary-phase estimate with no extra
regularity premise. -/
theorem uniformShiftEq117StationaryFor_of_cutoffs
    {chi rho : Real → Real} (hchi : IsDyadicPartition chi)
    (hrho : IsSmoothWeight rho 4 5) :
    UniformShiftEq117StationaryFor chi rho :=
  uniformShiftEq117StationaryFor_of_regular hchi
    (section12Eq117RegularityFor_of_cutoffs hchi hrho)

/-- The canonical Section 12 cutoffs satisfy the regularity interface
unconditionally. -/
theorem canonical_section12Eq117Regularity :
    Section12Eq117RegularityFor canonicalDyadicPartition
      iwaniecMozzochiSection6Weight :=
  section12Eq117RegularityFor_of_cutoffs
    canonicalDyadicPartition_isDyadicPartition
    iwaniecMozzochiSection6Weight_isSmoothWeight

/-- The canonical cutoffs therefore have the full pointwise (11.7)
specialization required at the entrance to Section 12. -/
theorem canonical_uniformShiftEq117Stationary :
    UniformShiftEq117StationaryFor canonicalDyadicPartition
      iwaniecMozzochiSection6Weight :=
  uniformShiftEq117StationaryFor_of_cutoffs
    canonicalDyadicPartition_isDyadicPartition
    iwaniecMozzochiSection6Weight_isSmoothWeight

end

end LeanProofs.IntegerPoints
