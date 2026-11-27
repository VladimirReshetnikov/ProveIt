import IPRADerivations.Analysis.Trigonometry.MultipleAngles.GaussianNamedSineMultipleAngleSamples
import IPRADerivations.Analysis.Trigonometry.SineProducts.Roots.GaussianSineTraceName
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate

/-!
# The multiple-angle identity on bounded Gaussian names

The trace is the original named sum of the two exponentials. Its
zero-safe recurrence is evaluated as a regular name, and the product
with the original sine agrees with the sine of the scaled argument.
The bound applies also when the initial sine vanishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 280000

namespace LeanProofs.IPRA.Analysis.GaussianNamedSineMultipleAngle

open_ipra
open GaussianBoundedIntegerExponentialSample (stage_input)
open GaussianBoundedIntegerExponentialStages (scaledF stageData radius)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono_one)
open GaussianEuclideanDistanceName (pointCN)
open GaussianExponentialInverse (negative_input)
open GaussianExponentialInverseSamples (positive negative disk inverseDisk positive_bound negative_bound positive_sample negative_sample baseNegativeRadius)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus multiply_fast product_distance sum_distance)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (negativeF negativeData add_sample_error multiply_sample_error)
open GaussianNamedSineFromExponential (sineF sineData sine_regular)
open GaussianNamedSineMultipleAngleSamples (baseRadius scaledRadius base_sample scaled_sample)
open GaussianRadiusExponentialName (input nameF data name_regular)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianSineMultipleAngleContinuity (growth value_bound value_distance)
open GaussianSineMultipleAngleRecurrence (value)
open GaussianSineSquaredTrace (sineValue)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def traceF (f : PR 2) : PR 2 := addF (nameF f) (nameF (negativeF f))
def traceData (R x : PTm n) : PTm n := addData (data R x) (data R (negativeData x))
def recurrenceF (f : PR 2) : PR 2 := GaussianSineTraceName.nameF (traceF f)
def recurrenceData (f : PR 2) (k R x : PTm n) : PTm n := GaussianSineTraceName.data (traceF f) k (traceData R x)
def multipleF (f : PR 2) : PR 2 := multiplyF (sineF f) (recurrenceF f)
def multipleData (f : PR 2) (k R x : PTm n) : PTm n := multiplyData (sineF f) (recurrenceF f) (sineData f R x) (recurrenceData f k R x)

ipra_subst traceData
ipra_subst recurrenceData
ipra_subst multipleData

theorem trace_regular (f : PR 2) (R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] pointCN (traceF f) (traceData R x) :=
  add_fast _ _ _ _ (name_regular f R x h) (name_regular (negativeF f) R (negativeData x) (negative_input f R x h))

theorem recurrence_regular (f : PR 2) (k R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] pointCN (recurrenceF f) (recurrenceData f k R x) :=
  GaussianSineTraceName.name_regular _ _ _ (trace_regular f R x h)

theorem multiple_regular (f : PR 2) (k R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] pointCN (multipleF f) (multipleData f k R x) :=
  multiply_fast _ _ _ _ (sine_regular f R x h) (recurrence_regular f k R x h)

def traceRadius (f : PR 2) (R x : PTm n) : PTm n := num 5+baseNegativeRadius f R x
def traceDisk (f : PR 2) (R x : PTm n) : PTm n :=
  GaussianNameBounds.U (traceF f) (traceData R x)+(disk R+inverseDisk f R x)

ipra_subst traceRadius
ipra_subst traceDisk

theorem trace_sample (f : PR 2) (p R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (traceF f) p (traceData R x)) (qadd (positive f p R x) (negative f p R x))
      (traceRadius f R x) (unit p) := by
  have hu := unit_positive (Γ := Γ) p
  have hneg := negative_input f R x h
  have first := add_sample_error (nameF f) (nameF (negativeF f)) (data R x) (data R (negativeData x)) p
    (name_regular f R x h) (name_regular (negativeF f) R (negativeData x) hneg)
  have last := sum_distance _ _ _ _ _ _ _ hu (positive_sample f p R x h) (negative_sample f p R x h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold traceRadius GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu first last)

private theorem trace_actual_bound (f : PR 2) (p R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (ap2 (traceF f) p (traceData R x)) (traceDisk f R x) one :=
  bounded_radius_mono_one (le_add_right _ _) (GaussianNameBounds.sample_bound _ _ _ (trace_regular f R x h))

private theorem trace_pair_bound (f : PR 2) (p R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] bounded (qadd (positive f p R x) (negative f p R x)) (traceDisk f R x) one :=
  bounded_radius_mono_one (le_add_left _ _)
    (bounded_sum_same _ _ _ _ _ (le_refl one) (positive_bound f p R x h) (negative_bound f p R x h))

def recurrenceRadius (f : PR 2) (k R x : PTm n) : PTm n :=
  (GaussianSineTraceName.modulus (traceF f) k (traceData R x)+one)+traceRadius f R x*growth (traceDisk f R x) k

ipra_subst recurrenceRadius [one]

theorem recurrence_sample (f : PR 2) (p k R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (recurrenceF f) p (recurrenceData f k R x))
      (value (qadd (positive f p R x) (negative f p R x)) k) (recurrenceRadius f k R x) (unit p) := by
  have first := GaussianSineTraceName.sample_error (traceF f) k p (traceData R x) (trace_regular f R x h)
  have mid := value_distance _ _ _ _ _ k (unit_positive p) (trace_actual_bound f p R x h) (trace_pair_bound f p R x h)
    (trace_sample f p R x h)
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p) first mid

def multipleRadius (f : PR 2) (k R x : PTm n) : PTm n :=
  (multiplyModulus (sineF f) (recurrenceF f) (sineData f R x) (recurrenceData f k R x)+one)+
    (baseRadius f R x*growth (traceDisk f R x) k+GaussianNameBounds.U (sineF f) (sineData f R x)*recurrenceRadius f k R x)

ipra_subst multipleRadius [one]

theorem multiple_sample (f : PR 2) (p k R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multipleF f) p (multipleData f k R x))
      (qmul (sineValue (positive f p R x) (negative f p R x)) (value (qadd (positive f p R x) (negative f p R x)) k))
      (multipleRadius f k R x) (unit p) := by
  let a := ap2 (sineF f) p (sineData f R x)
  let b := ap2 (recurrenceF f) p (recurrenceData f k R x)
  let A := sineValue (positive f p R x) (negative f p R x)
  let B := value (qadd (positive f p R x) (negative f p R x)) k
  have hp := unit_positive (Γ := Γ) p
  have hs := sine_regular f R x h
  have hr := recurrence_regular f k R x h
  have first := multiply_sample_error (sineF f) (recurrenceF f) (sineData f R x) (recurrenceData f k R x) p hs hr
  have da := distance_symmetric _ _ _ _ hp (base_sample f p R x h)
  have db := distance_symmetric _ _ _ _ hp (recurrence_sample f p k R x h)
  have second := product_distance A a B b _ _ _ (growth (traceDisk f R x) k) (GaussianNameBounds.U (sineF f) (sineData f R x))
    hp da db (value_bound _ _ _ (trace_pair_bound f p R x h)) (GaussianNameBounds.sample_bound _ _ _ hs)
  exact distance_triangle_same _ _ _ _ _ _ hp first (distance_symmetric _ _ _ _ hp second)

def identityRadius (f : PR 2) (E k R x : PTm n) : PTm n := scaledRadius f E k R x+multipleRadius f k R x

ipra_subst identityRadius

theorem identity_at (f : PR 2) (p E k R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) (hi : Γ ⊢[PRAAx] le (succ k) E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (sineF (scaledF f)) p (sineData (scaledF f) (radius E R) (stageData E (succ k) x)))
      (ap2 (multipleF f) p (multipleData f k R x)) (identityRadius f E k R x) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (scaled_sample f p E k R x h hi) (distance_symmetric _ _ _ _ (unit_positive p) (multiple_sample f p k R x h))

theorem identity (f : PR 2) (E k R x : PTm n) (h : Γ ⊢[PRAAx] input f R x) (hi : Γ ⊢[PRAAx] le (succ k) E) :
    Γ ⊢[PRAAx] crossEquivalent (sineF (scaledF f)) (multipleF f)
      (sineData (scaledF f) (radius E R) (stageData E (succ k) x)) (multipleData f k R x) := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (identityRadius f E k R x)
    (sine_regular _ _ _ (stage_input f E (succ k) R x h hi)) (multiple_regular f k R x h)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have his : Γ.map Fm.shift ⊢[PRAAx] le (succ (Syn.shift k)) (Syn.shift E) := by
    simpa only [Fm.shift,subst_le,Syn.shift,ConciseIPRA.PTm.subst_succ] using hi.shift
  simpa only [GaussianNamedDiagonalRate.diagonalRate,Syn.shift,subst_identityRadius,subst_multipleData,
    GaussianNamedSineFromExponential.subst_sineData,GaussianBoundedIntegerExponentialStages.subst_radius,
    GaussianBoundedIntegerExponentialStages.subst_stageData,ConciseIPRA.PTm.subst_succ] using
    identity_at f (var 0) (Syn.shift E) (Syn.shift k) (Syn.shift R) (Syn.shift x) hs his

theorem actual_bounded_named_sine_multiple_angle_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input f (var 2) (var 3) ⟶ le (succ (var 1)) (var 0) ⟶
      crossEquivalent (sineF (scaledF f)) (multipleF f)
        (sineData (scaledF f) (radius (var 0) (var 2)) (stageData (var 0) (succ (var 1)) (var 3)))
        (multipleData f (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (identity f _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedSineMultipleAngle
