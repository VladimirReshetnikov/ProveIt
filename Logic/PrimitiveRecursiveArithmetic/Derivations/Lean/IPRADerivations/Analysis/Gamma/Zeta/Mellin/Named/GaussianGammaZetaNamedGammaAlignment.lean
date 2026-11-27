import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaNamedChart
import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaNamedInput
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneDemandComparison
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedPoleFreeEncoding
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Terminal.GaussianGammaNegativeIntervalNamedTerminalProperness

/-!
# The Gamma factor agrees with the original named evaluator

At a common late input observation, the original shifted evaluator and
the signed Gamma chart read exactly the same complex rational. Their
native Gamma names agree by encoding and radius independence.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedGammaAlignment

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedShiftInput (shiftF shiftData)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianGammaZetaNamedChart (gammaMap gammaDataF gamma_data_at)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)
open GaussianNamedRightHalfPlaneLift (source data)
open GaussianNamedRightHalfPlaneSigned (certificate native_value)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_two_errors_same distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian canonical_unique ofGaussian_canonical ofGaussian_represents represents_congr positive_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)
open GaussianRootAlgebra (equal_refl)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem frozen_cross (f : PR 2) (p t x M R : PTm n)
    (hq : Γ ⊢[PRAAx] certificate (ap2 f (GaussianEulerNamedShiftInput.clock t) x) R (two*M))
    (hG : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input (shiftF f) p t (shiftData x) M) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF
      (GaussianNamedRightHalfPlaneDemandLift.frozenData gammaMap f (GaussianEulerNamedShiftInput.clock t) x M R)
      (GaussianNamedGammaLateInput.encodedData (shiftF f) t (shiftData x) M) := by
  let q := ap2 f (GaussianEulerNamedShiftInput.clock t) x
  let r := ap2 (shiftF f) t (shiftData x)
  let B := GaussianGammaZetaNamedChart.denominator q
  let W := GaussianGammaZetaNamedChart.radius R+one
  let A := GaussianGammaZetaNamedChart.degree (two*M)
  let z := shifted (GaussianGammaZetaNamedChart.numerator q) B
  let w := shifted (rawGaussian q) B
  have hs := GaussianGammaZetaDirichletPowerOrder.shifted_source
    (GaussianGammaZetaNamedChart.numerator q) (GaussianGammaZetaNamedChart.radius R) B A (GaussianGammaZetaNamedChart.native_source q R (two*M) hq)
  have hb := hs.andE₁.andE₂.andE₁.andE₁
  have equal := GaussianGammaInputProperness.translated_equal (GaussianGammaZetaNamedChart.numerator q) (rawGaussian q) B one
    (native_value q hq.andE₁.andE₁.andE₁.andE₁)
  have eq : Γ ⊢[PRAAx] ofGaussian w B ≐ ofGaussian z B :=
    canonical_unique _ _ z B (ofGaussian_canonical _ _ hb) (ofGaussian_canonical _ _ hb) hb
      (represents_congr (.eqRefl _) (GaussianRootAlgebra.equal_symm equal) (.eqRefl _) (ofGaussian_represents w B hb))
      (ofGaussian_represents z B hb)
  have read : Γ ⊢[PRAAx] r ≐ ofGaussian z B :=
    (GaussianEulerNamedShiftInput.sample_fraction f t x).eqTrans eq
  have gz := GaussianGammaHalfPlaneInputContinuity.reciprocal_source z W B A hs
  have raw := GaussianGammaNamedPoleFreeEncoding.raw_source_of_fraction r z W B one A gz read
  have same := GaussianGammaNamedPoleFreeEncoding.raw_gamma_cross r z W B A gz read
  let S := GaussianNamedRightHalfPlane.radius (shiftF f) (shiftData x)
  have later := GaussianGammaHalfPlaneInputContinuity.reciprocal_source (rawGaussian r) S (rawDen r) (two*M)
    (GaussianNamedGammaLateInput.encoded_source (shiftF f) p t (shiftData x) M hG)
  have sameRadius := GaussianGammaRadiusOverlap.original_Gamma_overlap (rawGaussian r) W S (rawDen r) one A one (two*M) raw later
  have eqAt := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ same) sameRadius
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr gammaF gammaF _ _ _ _
    (gamma_data_at q R (two*M)).eqSymm (.eqRefl _) eqAt

private theorem at_same_clock (F H : PR 2) (p x y : PTm n)
    (h : Γ ⊢[PRAAx] independentRate F H x y one (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 H p y) (num 3) (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ hp) hp
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring))
    (rate_at F H x y one (unit p) p p h)

theorem original_observations (f : PR 2) (p x M R : PTm n) (hf : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (GaussianNamedRightHalfPlaneDemandLift.nameF gammaMap f) p (data x M R))
      (ap2 (GaussianNamedGamma.nameF (shiftF f)) p (GaussianNamedGamma.data (shiftData x) M)) (num 8) (unit p) := by
  let a := GaussianNamedRightHalfPlaneDemandLift.clock gammaMap p M R
  let b := GaussianNamedGamma.clock (shiftF f) p (shiftData x) M
  let t := a+b
  let k := GaussianEulerNamedShiftInput.clock t
  let X := GaussianNamedRightHalfPlaneDemandLift.frozenData gammaMap f k x M R
  let Y := GaussianNamedGammaLateInput.encodedData (shiftF f) t (shiftData x) M
  have hA : Γ ⊢[PRAAx] le a k := le_trans (le_add_right a b) (GaussianEulerNamedShiftInput.clock_later t)
  have hB : Γ ⊢[PRAAx] le b t := le_add_left b a
  have hq := GaussianNamedRightHalfPlaneLift.late_certificate f x k M R hf
    (le_trans (GaussianNamedRightHalfPlaneDemandLift.clock_margin gammaMap p M R) hA)
  have hG : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input (shiftF f) p t (shiftData x) M :=
    .andI (GaussianEulerNamedShiftInput.original_source f x M hf.andE₁)
      (.andI (le_trans (GaussianNamedGamma.clock_margin (shiftF f) p (shiftData x) M) hB)
        (le_trans (GaussianNamedGamma.clock_demand (shiftF f) p (shiftData x) M p (le_succ_self p)) hB))
  have hx := GaussianNamedRightHalfPlaneDemandComparison.frozen_rate gammaMap f p k x M R hf hA
  have hy := GaussianNamedGammaLateInput.original_independent_rate (shiftF f) p t (shiftData x) M hG
  have boundL := at_same_clock _ _ p (data x M R) X hx
  have hp := unit_positive (Γ := Γ) p
  have boundR := distance_symmetric _ _ _ _ hp (at_same_clock _ _ p (GaussianNamedGamma.data (shiftData x) M) Y hy)
  have middle := distance_two_errors_same hp
    (cross_at gammaF gammaF X Y p p (frozen_cross f p t x M R hq hG))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp boundL (distance_triangle_same _ _ _ _ _ _ hp middle boundR))

theorem equivalent (f : PR 2) (x M R : PTm n) (hf : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedRightHalfPlaneDemandLift.nameF gammaMap f) (GaussianNamedGamma.nameF (shiftF f)) (data x M R) (GaussianNamedGamma.data (shiftData x) M) := by
  have hs := GaussianEulerNamedShiftInput.original_source f x M hf.andE₁
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 8)
    (GaussianNamedRightHalfPlaneDemandLift.name_regular gammaMap f x M R hf) (GaussianNamedGamma.name_regular (shiftF f) (shiftData x) M hs) (.allI ?_)
  let sh (z : PTm n) := Syn.shift z
  have h : Γ.map Fm.shift ⊢[PRAAx] source f (sh x) (sh M) (sh R) := by
    simpa [Fm.shift,Syn.shift,sh] using hf.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,sh,
    GaussianNamedRightHalfPlaneLift.subst_data,GaussianNamedGamma.subst_data,GaussianEulerNamedShiftInput.subst_shiftData,PTm.subst_num] using
    original_observations f (var 0) (sh x) (sh M) (sh R) h

theorem equivalent_at_argument (f : PR 2) (x M : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaZetaNamedInput.source f x M) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedRightHalfPlaneDemandLift.nameF gammaMap (GaussianGammaZetaNamedInput.minusOneF f)) (GaussianNamedGamma.nameF f)
      (data (GaussianGammaZetaNamedInput.minusOneData x) M (GaussianGammaZetaNamedInput.radius f x)) (GaussianNamedGamma.data x M) := by
  let F := GaussianGammaZetaNamedInput.minusOneF f
  let X := GaussianGammaZetaNamedInput.minusOneData x
  let R := GaussianGammaZetaNamedInput.radius f x
  let u := GaussianNamedRightHalfPlane.marginPoint M
  have hs := GaussianEulerNamedShiftInput.original_source F X M (GaussianGammaZetaNamedInput.original_source f x M h)
  have hr := GaussianGammaZetaNamedInput.original_restored f x h.andE₁
  have cert : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.certificate f x M :=
    GaussianNamedRealOrderTransport.transport constantF constantF (shiftF F) f u u (shiftData X) x
      (cross_refl _ _ (constant_regular u)) hr hs.andE₂.andE₂
  have orig : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x M := .andI h.andE₁ (.andI h.andE₂.andE₁ cert)
  exact cross_trans _ _ _ _ _ _ (equivalent F X M R (GaussianGammaZetaNamedInput.lift_source f x M h))
    (GaussianGammaNegativeIntervalNamedTerminalDerivative.original_gamma_proper (shiftF F) f (shiftData X) x M M hs orig hr)

theorem actual_original_named_Gamma_factor_at_argument_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (GaussianGammaZetaNamedInput.source f (var 0) (var 1) ⟶
        crossEquivalent (GaussianNamedRightHalfPlaneDemandLift.nameF gammaMap (GaussianGammaZetaNamedInput.minusOneF f)) (GaussianNamedGamma.nameF f)
          (data (GaussianGammaZetaNamedInput.minusOneData (var 0)) (var 1) (GaussianGammaZetaNamedInput.radius f (var 0)))
          (GaussianNamedGamma.data (var 0) (var 1))) :=
  closeUniv 2 (.impI (equivalent_at_argument f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedGammaAlignment
