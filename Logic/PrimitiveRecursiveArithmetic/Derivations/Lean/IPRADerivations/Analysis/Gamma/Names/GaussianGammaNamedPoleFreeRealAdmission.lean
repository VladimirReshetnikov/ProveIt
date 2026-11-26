import IPRADerivations.Analysis.Gamma.Names.GaussianGammaNamedPoleFreeNegativeSnapshot
import IPRADerivations.Analysis.Gamma.NegativeAxis.GaussianGammaNegativeIntervalNamedGammaNativeDomain
import IPRADerivations.Analysis.Names.GaussianNamedPositiveLateLogSource
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaIncrementInput
import IPRADerivations.Analysis.RationalArithmetic.RationalCompactObservationTightening

/-!
# Real Gamma charts away from the poles

A computed real observation determines either a positive margin or a
negative unit interval. In the second case the original rational pole
margins survive retiming and translation. Translating back gives the
original real name at independent observation clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeRealAdmission

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction_order pointCN)
open GaussianExponentialReference (recode_fixed unit_monotone)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaNamedPoleFreeNegativeSnapshot (interval offsetNumerator nonpositiveAt finite_window)
open GaussianGammaNamedPoleFreePositiveAdmission (nonnegativeAt positive_source)
open GaussianGammaNegativeIntervalNamedGammaNativeDomain (shiftF shiftData shift_at)
open GaussianNameArithmetic (addF addData add_at add_fast recode_congr)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianNamedRightHalfPlane (threshold threshold_budget numerator denominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qadd qadd_canonical positive_product)
open GaussianRationalL1 (raw_den_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at subst_realSamples)
open GaussianStirlingMultiplicativeBoundsOrder (fraction_real_part)
open GaussianUnitIntervalInputDecoding (lowerPoint upperPoint)
open RationalArgmin (rationalLE_congr)
open RationalCompactObservationTightening (lower_guard upper_guard)
open RationalGaussianEmbedding (axis_congr axis_add)
open RationalValueBounds (upper upper_congr upper_triangle upper_of_order upper_of_radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "poleSource" => GaussianGammaNamedPoleFree.source
local notation "unitSource" => GaussianNamedEulerUnitTime.source

def snapshot (E : PTm n) : PTm n := threshold (two*E)
def chartIndex (f : PR 2) (x E : PTm n) : PTm n := interval f (snapshot E) x
def offsetF (f : PR 2) : PR 2 := addF (retimedF f) constantF
def offsetData (f : PR 2) (x E : PTm n) : PTm n :=
  addData (retimedData x (two*E)) (naturalPoint (succ (chartIndex f x E)))
def readClock (p E : PTm n) : PTm n := GaussianNamedGammaIncrementInput.clock p+snapshot E

@[simp] theorem subst_snapshot {m : ℕ} (σ : Fin n → PTm m) (E : PTm n) :
    Syn.subst σ (snapshot E) = snapshot (Syn.subst σ E) := by simp [snapshot,two,one]
@[simp] theorem subst_chartIndex {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E : PTm n) :
    Syn.subst σ (chartIndex f x E) = chartIndex f (Syn.subst σ x) (Syn.subst σ E) := by
  simp only [chartIndex,interval,GaussianGammaNamedPoleFreeNegativeSnapshot.magnitude,subst_ap2,
    Foundations.GapDecision.subst_zabs,ComplexLogarithmRemainder.subst_re,GaussianNamedRightHalfPlane.subst_numerator,
    GaussianNamedRightHalfPlane.subst_denominator,subst_snapshot]
@[simp] theorem subst_offsetData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E : PTm n) :
    Syn.subst σ (offsetData f x E) = offsetData f (Syn.subst σ x) (Syn.subst σ E) := by
  simp [offsetData,two,one]

theorem offset_at (f : PR 2) (p x E : PTm n) : Γ ⊢[PRAAx]
    ap2 (offsetF f) p (offsetData f x E) ≐
      qadd (ap2 f (readClock p E) x) (naturalPoint (succ (chartIndex f x E))) := by
  let k := GaussianNamedGammaIncrementInput.clock p
  let c := naturalPoint (succ (chartIndex f x E))
  let u := retimedData x (two*E)
  have read := qadd_congr (GaussianNamedPositiveLateLogSource.sample_at (Γ := Γ) f k x (two*E)) (constant_at k c)
  exact (add_at (retimedF f) constantF u c p).eqTrans
    ((recode_congr read).eqTrans (recode_fixed _ (qadd_canonical _ _)))

theorem offset_regular (f : PR 2) (x E : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (offsetF f) (offsetData f x E) :=
  add_fast _ _ _ _ (GaussianNamedPositiveLateLogSource.name_regular f x (two*E) hf) (constant_regular _)

private theorem snapshot_fraction (f : PR 2) (x R E : PTm n) (h : Γ ⊢[PRAAx] poleSource f x R E)
    (hr : Γ ⊢[PRAAx] realSamples f x) (hs : Γ ⊢[PRAAx] nonpositiveAt f (snapshot E) x) :
    Γ ⊢[PRAAx] qadd (ap2 f (snapshot E) x) (naturalPoint (succ (chartIndex f x E))) ≐
      fraction (offsetNumerator f (snapshot E) x) (denominator f (snapshot E) x) := by
  let s := snapshot E
  let j := succ (chartIndex f x E)
  let q := ap2 f s x
  let z := numerator f s x
  let B := denominator f s x
  let a := offsetNumerator f s x
  let w := GaussianEulerParameterExponentialIncrement.shifted z B (scale j oneCode) one
  have axes := (finite_window f s x R E h hr hs).andE₂
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal w (scale a oneCode) := by
    have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal w (GaussianGammaEulerHeadLower.translated z B j) := by
      apply GaussianRootAlgebra.equal_of_values <;>
        simp only [w,GaussianEulerParameterExponentialIncrement.shifted,GaussianGammaEulerHeadLower.translated,
          GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,GaussianRootAlgebra.re_scale,
          GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring
    apply GaussianRootAlgebra.equal_of_values
    · have first := (GaussianRootAlgebra.equal_re e).trans (ZT.toZ_eq axes.andE₁)
      simpa only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat,_root_.mul_one] using first
    · have first := (GaussianRootAlgebra.equal_im e).trans (ZT.toZ_eq axes.andE₂)
      simp only [ZT.toZ_ofNat,Q.mk_zero,map_zero] at first
      rw [GaussianRootAlgebra.im_scale,GaussianRootAlgebra.im_one,first]
      ring
  have hb : Γ ⊢[PRAAx] le one B := raw_den_positive q
  have rep := GaussianNamedGammaIncrementInput.sum_represents (Γ := Γ) q (scale j oneCode) one (le_refl one)
  exact GaussianRationalHorner.canonical_unique _ _ (scale a oneCode) B (qadd_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hb) hb
    (GaussianRationalHorner.represents_congr (.eqRefl _) same ((mul_comm B one).eqTrans (one_mul B)) rep)
    (GaussianRationalHorner.ofGaussian_represents _ _ hb)

private theorem snapshot_source (f : PR 2) (x R E : PTm n) (h : Γ ⊢[PRAAx] poleSource f x R E)
    (hr : Γ ⊢[PRAAx] realSamples f x) (hs : Γ ⊢[PRAAx] nonpositiveAt f (snapshot E) x) :
    Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source
      (qadd (ap2 f (snapshot E) x) (naturalPoint (succ (chartIndex f x E)))) E := by
  let s := snapshot E
  let a := offsetNumerator f s x
  let B := denominator f s x
  let q := qadd (ap2 f s x) (naturalPoint (succ (chartIndex f x E)))
  have H := (finite_window f s x R E h hr hs).andE₁
  have hb : Γ ⊢[PRAAx] le one B := raw_den_positive _
  have he := H.andE₂.andE₁
  have same : Γ ⊢[PRAAx] q ≐ fraction a B := snapshot_fraction f x R E h hr hs
  have lo := fraction_order one E a B he hb
    (le_congr (by ipra_ring) (by ipra_ring) H.andE₂.andE₂.andE₁)
  have er := natEq (eq_add_of_le he)
  have c : Γ ⊢[PRAAx] le (a*E+B) (monus E one*B+B) := by
    refine le_congr (by ipra_ring) ?_ H.andE₂.andE₂.andE₂
    apply deriveNat
    ipra_simps
    linear_combination 𝔞 B*er
  have hi := fraction_order a B (monus E one) E hb he
    (le_congr (mul_comm _ _) (.eqRefl _) (le_of_add_le_add_right c))
  have coord := (congrFst same).eqTrans (fraction_real_part a B hb)
  exact .andI (axis_congr same.eqSymm (GaussianStirlingNames.fraction_axis a B hb)) (.andI he
    (.andI (upper_of_order _ _ _ _ (rationalLE_congr (.eqRefl _) coord.eqSymm lo))
      (upper_of_order _ _ _ _ (rationalLE_congr coord.eqSymm (.eqRefl _) hi))))

private theorem retimed_distance (f : PR 2) (p x E : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f (snapshot E) x) (ap2 f (readClock p E) x) one (two*E) := by
  let k := snapshot E
  let j := readClock p E
  let U := unit k
  let V := unit j
  let M := two*E
  have hU : Γ ⊢[PRAAx] le (two*M) U := threshold_budget k M (le_refl _)
  have hV : Γ ⊢[PRAAx] le (two*M) V := threshold_budget j M (le_add_left _ _)
  have a := mul_le_mul_right U hV
  have b := mul_le_mul_right V hU
  have budget : Γ ⊢[PRAAx] le ((U+V)*M) (one*(U*V)) :=
    RationalValueBounds.positive_cancel RationalAlgebra.two_positive
      (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ a b))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive k) (unit_positive j))
    (positive_product _ _ RationalAlgebra.two_positive hE) budget (point_at f x k j hf)

theorem offset_source_at (f : PR 2) (p x R E : PTm n) (h : Γ ⊢[PRAAx] poleSource f x R E)
    (hr : Γ ⊢[PRAAx] realSamples f x) (hs : Γ ⊢[PRAAx] nonpositiveAt f (snapshot E) x) :
    Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source (ap2 (offsetF f) p (offsetData f x E)) (two*E) := by
  let M := two*E
  let c := naturalPoint (succ (chartIndex f x E))
  let u := ap2 f (snapshot E) x
  let v := ap2 f (readClock p E) x
  let y := qadd u c
  let z := qadd v c
  have original := snapshot_source f x R E h hr hs
  have hE := original.andE₂.andE₁
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ RationalAlgebra.two_positive hE
  have close : Γ ⊢[PRAAx] distanceBounded y z one M :=
    GaussianNameRingLaws.sum_left_error u v c one M hM (retimed_distance f p x E h.andE₁ hE)
  have lo := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hM close)
  have hi := upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hM (distance_symmetric _ _ _ _ hM close))
  have lo' : Γ ⊢[PRAAx] upper (lowerPoint E) (fstT z) one M :=
    upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (upper_triangle _ _ _ _ _ _ _ original.andE₂.andE₂.andE₁ lo)
  have hi' : Γ ⊢[PRAAx] upper (fstT z) (upperPoint E) one M :=
    upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (upper_triangle _ _ _ _ _ _ _ hi original.andE₂.andE₂.andE₂)
  have lc := lower_guard (fstT z) E M M hE (le_refl M) (le_refl M) lo'
  have uc := upper_guard (fstT z) E M M hE (le_refl M) (le_refl M) hi'
  have hc : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis c :=
    GaussianStirlingNames.fraction_axis _ one (le_refl one)
  have real := axis_add v c (real_sample_at f x (readClock p E) hr).andE₂ hc
  have read := offset_at (Γ := Γ) f p x E
  exact .andI (axis_congr read.eqSymm real) (.andI hM
    (.andI (upper_congr (.eqRefl _) (congrFst read).eqSymm (.eqRefl _) (.eqRefl _) lc)
      (upper_congr (congrFst read).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) uc)))

theorem offset_source (f : PR 2) (x R E : PTm n) (h : Γ ⊢[PRAAx] poleSource f x R E)
    (hr : Γ ⊢[PRAAx] realSamples f x) (hs : Γ ⊢[PRAAx] nonpositiveAt f (snapshot E) x) :
    Γ ⊢[PRAAx] unitSource (offsetF f) (offsetData f x E) (two*E) := by
  refine .andI (offset_regular f x E h.andE₁) (.allI ?_)
  let Δ := Γ.map Fm.shift
  let sh (t : PTm n) := Syn.shift t
  have f' : Δ ⊢[PRAAx] poleSource f (sh x) (sh R) (sh E) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  have r' : Δ ⊢[PRAAx] realSamples f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hr.shift
  have s' : Δ ⊢[PRAAx] nonpositiveAt f (snapshot (sh E)) (sh x) := by
    simpa [Δ,sh,Fm.shift,Syn.shift,nonpositiveAt,ConciseIPRA.PTm.subst_zero] using hs.shift
  simpa only [GaussianNamedEulerUnitKernel.admissibleSamples,Syn.shift,sh,subst_offsetData,
    LeanProofs.IPRA.PTm.subst_mul,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,two,one] using
    offset_source_at f (var 0) (sh x) (sh R) (sh E) f' r' s'

theorem shifted_back_at (f : PR 2) (p x E : PTm n) (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] ap2 (shiftF (offsetF f)) p (shiftData (offsetData f x E) (chartIndex f x E)) ≐ ap2 f (readClock p E) x := by
  let d := offsetData f x E
  let J := chartIndex f x E
  let c := naturalPoint (succ J)
  let q := ap2 f (readClock p E) x
  have sum := (recode_congr (offset_at (Γ := Γ) f p x E)).eqTrans (recode_fixed _ (qadd_canonical q c))
  exact (shift_at (offsetF f) p d J).eqTrans
    ((qsub_congr sum (.eqRefl _)).eqTrans
      ((qsub_congr (GaussianReciprocalHorner.qadd_commutative q c) (.eqRefl _)).eqTrans
        (qadd_sub_cancel c q (real_sample_at f x (readClock p E) hr).andE₁)))

private theorem shifted_back_observations (f : PR 2) (p q x E : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (shiftF (offsetF f)) p (shiftData (offsetData f x E) (chartIndex f x E)))
      (ap2 f q x) (unit p+unit q) (unit p*unit q) := by
  let k := readClock p E
  have later : Γ ⊢[PRAAx] le (unit p) (unit k) :=
    unit_monotone (le_trans (GaussianNamedGammaIncrementInput.clock_later p) (le_add_right _ _))
  have hQ := unit_positive (Γ := Γ) q
  have hP := unit_positive (Γ := Γ) p
  have hK := unit_positive (Γ := Γ) k
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hK hQ) (positive_product _ _ hP hQ) ?_
    (distance_congr (shifted_back_at f p x E hr).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (point_at f x k q hf))
  ipra_le 𝔞 (unit q*unit q)*sl later

theorem shifted_back_cross (f : PR 2) (x E : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] crossEquivalent (shiftF (offsetF f)) f (shiftData (offsetData f x E) (chartIndex f x E)) x := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have h : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have r : Δ ⊢[PRAAx] realSamples f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hr.shift.shift
  simpa only [crossEquivalent,GaussianGammaNegativeIntervalNamedGammaNativeDomain.subst_shiftData,
    subst_offsetData,subst_chartIndex,sh,Syn.shift] using
    shifted_back_observations f (var 1) (var 0) (sh x) (sh E) h r

def negativeChart (f : PR 2) (x E : PTm n) : Fm PTm n :=
  unitSource (offsetF f) (offsetData f x E) (two*E) ⋏
    crossEquivalent (shiftF (offsetF f)) f (shiftData (offsetData f x E) (chartIndex f x E)) x

theorem real_admission (f : PR 2) (x R E : PTm n)
    (h : Γ ⊢[PRAAx] poleSource f x R E) (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] GaussianNamedGammaPositiveLower.source f x (two*E) ⋎ negativeChart f x E := by
  let t := snapshot E
  have stronger : Γ ⊢[PRAAx] le (two*(two*E)) (unit t) := threshold_budget t (two*E) (le_refl _)
  have weaker : Γ ⊢[PRAAx] le (two*E) (two*(two*E)) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_add_right (two*E) (two*E))
  have late := le_trans weaker stronger
  refine .orE (PolynomialBisection.zle_total (ZT.ofNat zero) (ComplexLogarithmRemainder.re (numerator f t x))) ?_ ?_
  · exact .orI₁ (positive_source f t x R E h.wk hr.wk Prf.hyp0 late.wk)
  · exact .orI₂ (.andI (offset_source f x R E h.wk hr.wk Prf.hyp0) (shifted_back_cross f x E h.andE₁.wk hr.wk))

theorem actual_pole_free_real_Gamma_chart_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((poleSource f (var 0) (var 1) (var 2) ⋏ realSamples f (var 0)) ⟶
        GaussianNamedGammaPositiveLower.source f (var 0) (two*var 2) ⋎ negativeChart f (var 0) (var 2)) :=
  closeUniv 3 (.impI (real_admission f _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeRealAdmission
