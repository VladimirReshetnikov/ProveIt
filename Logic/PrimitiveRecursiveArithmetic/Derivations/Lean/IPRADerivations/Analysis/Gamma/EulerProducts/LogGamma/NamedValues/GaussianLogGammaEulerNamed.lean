import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.RationalCharts.GaussianLogGammaEulerCommonDenominator
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.RationalCharts.GaussianLogGammaEulerRationalContinuity
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.RationalCharts.GaussianLogGammaEulerRescale
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneLift

/-!
# Canonical cofinal log-Gamma on regular right-half-plane names

The continuity test works at the literal common denominator of two
signed rational observations. Rescaling preserves both original Euler
limits, so the lift uses the original rational evaluator on each sample.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamed

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianLogGammaEulerCofinal (canonicalData)
open GaussianLogGammaEulerCommonDenominator
  (commonReal commonImag common_sources common_arguments common_size continuityRadius
    continuity_radius_from_distance displacement sizeBound)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerRationalContinuity (local_guard widened_rate)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianNamedRightHalfPlaneSigned
  (certificate denominator imagNumerator point realNumerator sign)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalL1 (raw_den_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalValueEquality (commonDen)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianLogGammaEulerCofinal.nameF
local notation "Lift" => GaussianNamedRightHalfPlaneLift.nameF

def pointData (z : PTm n) : PTm n :=
  canonicalData (realNumerator z) (imagNumerator z) (denominator z) (sign z)

def rationalData : PR 1 := PTm.toPR (pointData (var 0) : PTm 1)

def coefficient (R K : PTm n) : PTm n :=
  GaussianLogGammaEulerRationalContinuity.gain K (sizeBound R R)

def gain : PR 2 := PTm.toPR (coefficient (var 0) (var 1) : PTm 2)

ipra_subst pointData [canonicalData]

theorem rational_data_at (z : PTm n) : Γ ⊢[PRAAx] ap1 rationalData z ≐ pointData z := by
  simpa only [rationalData, ap1, subst_pointData, Syn.subst_var, Matrix.cons_val_zero] using
    toPR_eq (Γ := Γ) (pointData (var 0) : PTm 1) ![z]

theorem gain_at (R K : PTm n) : Γ ⊢[PRAAx] ap2 gain R K ≐ coefficient R K := by
  simpa only [gain, ap2, coefficient, GaussianLogGammaEulerRationalContinuity.subst_gain,
    GaussianLogGammaEulerCommonDenominator.subst_sizeBound, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one] using toPR_eq (Γ := Γ) (coefficient (var 0) (var 1) : PTm 2) ![R,K]

theorem original_chart (q r R S K : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K) : Γ ⊢[PRAAx]
    crossEquivalent F F (canonicalData (commonReal q r) (commonImag q r) (commonDen q r) (sign q)) (pointData q) ⋏
      crossEquivalent F F (canonicalData (commonReal r q) (commonImag r q) (commonDen q r) (sign r)) (pointData r) := by
  have e := common_arguments q r R S K hq hr
  exact .andI
    (GaussianLogGammaEulerRescale.canonical_rescale (realNumerator q) (imagNumerator q) (denominator q) (sign q)
      (denominator r) (commonDen q r) hq.andE₁.andE₁ (raw_den_positive r) (mul_comm (denominator r) (denominator q))
      (e.andE₁.eqTrans hq.andE₂.andE₂.eqSymm))
    (GaussianLogGammaEulerRescale.canonical_rescale (realNumerator r) (imagNumerator r) (denominator r) (sign r)
      (denominator q) (commonDen q r) hr.andE₁.andE₁ (raw_den_positive q) (.eqRefl _)
      (e.andE₂.eqTrans hr.andE₂.andE₂.eqSymm))

private theorem observation_distance (x y E D : PTm n)
    (hx : Γ ⊢[PRAAx] le one (realNumerator x)) (hy : Γ ⊢[PRAAx] le one (realNumerator y))
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded (point x) (point y) E D) :
    Γ ⊢[PRAAx] distanceBounded x y E D := by
  have xzero := GaussianNamedRightHalfPlaneSigned.point_distance_raw x hx
  have yzero := GaussianNamedRightHalfPlaneSigned.point_distance_raw y hy
  have left := distance_radius_mono _ _ zero one zero D (le_refl one) hD (by ipra_le 0)
    (distance_symmetric _ _ _ _ (le_refl one) xzero)
  have right := distance_radius_mono _ _ zero one zero D (le_refl one) hD (by ipra_le 0) yzero
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD left h) right)

theorem original_variation (x y R K E D : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hD : Γ ⊢[PRAAx] le one D) (small : Γ ⊢[PRAAx] le (coefficient R K * E) D)
    (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) E D) :
    Γ ⊢[PRAAx] independentRate F F (pointData x) (pointData y) (coefficient R K * E) D := by
  let d := commonDen y x
  let C := sizeBound R R
  let H := continuityRadius (displacement y x)
  let A := commonReal y x
  let B := commonImag y x
  let a := commonReal x y
  let b := commonImag x y
  have hxy := observation_distance x y E D hx.andE₁.andE₁.andE₁.andE₁ hy.andE₁.andE₁.andE₁.andE₁ hD near
  have hK := GaussianDominantScalarOrder.factor_positive_left K (realNumerator x)
    (le_trans hx.andE₁.andE₁.andE₂ hx.andE₂.andE₁)
  have hs := common_sources y x R R K hy hx
  have hStep := continuity_radius_from_distance y x R R K E D hy hx hD hxy
  have ht : Γ ⊢[PRAAx] GaussianLogGammaEulerTaylorUniform.source A B (sign y) a b (sign x) d H K C :=
    .andI hs.andE₁.andE₁ (.andI hs.andE₂.andE₁.andE₁ (.andI hStep.andE₁
      (.andI hK (.andI hs.andE₂.andE₂.andE₁ (.andI hs.andE₂.andE₂.andE₂
        (.andI (common_size y x R R K hy hx) (local_guard H E K C d D hD hStep.andE₂ small)))))))
  have rate := widened_rate A B (sign y) a b (sign x) d H K C E D ht hD hStep.andE₂
  have chart := original_chart y x R R K hy hx
  exact GaussianNamedRateTransport.transport F F F F _ _ _ _ _ _ hD rate
    (cross_symm _ _ _ _ chart.andE₂) (cross_symm _ _ _ _ chart.andE₁)

theorem variation (x y R K E D : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hD : Γ ⊢[PRAAx] le one D) (small : Γ ⊢[PRAAx] le (ap2 gain R K * E) D)
    (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) E D) :
    Γ ⊢[PRAAx] independentRate F F (ap1 rationalData x) (ap1 rationalData y) (ap2 gain R K * E) D := by
  have eq := congrMul (gain_at (Γ := Γ) R K) (.eqRefl E)
  have rate := original_variation x y R K E D hx hy hD (le_congr eq (.eqRefl _) small) near
  let formula : Fm PTm 4 := independentRate F F (var 0) (var 1) (var 2) (var 3)
  have result := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) formula
    ![pointData x,pointData y,coefficient R K*E,D] ![ap1 rationalData x,ap1 rationalData y,ap2 gain R K*E,D]
    (fun i => by
      fin_cases i
      · exact (rational_data_at x).eqSymm
      · exact (rational_data_at y).eqSymm
      · exact eq.eqSymm
      · exact .eqRefl D)
    (by simpa only [formula,subst_independentRate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using rate)
  simpa only [formula,subst_independentRate,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using result

def rationalMap : GaussianNamedRightHalfPlaneLift.RationalMap where
  evaluator := F
  rationalData := rationalData
  gain := gain
  variation := variation

abbrev source (f : PR 2) (x M R : PTm n) : Fm PTm n := GaussianNamedRightHalfPlaneLift.source f x M R
abbrev nameF (f : PR 2) : PR 2 := Lift rationalMap f
abbrev data (x M R : PTm n) : PTm n := GaussianNamedRightHalfPlaneLift.data x M R

theorem name_regular (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x M R) :=
  GaussianNamedRightHalfPlaneLift.name_regular rationalMap f x M R h

theorem proper (f g : PR 2) (x y M R : PTm n)
    (hx : Γ ⊢[PRAAx] source f x M R) (hy : Γ ⊢[PRAAx] source g y M R)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x M R) (data y M R) :=
  GaussianNamedRightHalfPlaneLift.proper rationalMap f g x y M R hx hy he

theorem late_rational_rate (f : PR 2) (s k x M R : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (GaussianNamedRightHalfPlaneLift.clock rationalMap s M R) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) F (data x M R) (ap1 rationalData (ap2 f k x))
      one (GaussianCoefficientNameBounds.unit s) :=
  GaussianNamedRightHalfPlaneLift.frozen_rate rationalMap f s k x M R h hk

theorem actual_named_complex_log_Gamma_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerNamed
