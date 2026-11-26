import IPRADerivations.Analysis.Logarithm.GaussianRightHalfPlaneLogarithmRationalContinuity
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerCommonDenominator
import IPRADerivations.Analysis.Names.GaussianNamedRightHalfPlaneLift

/-!
# Canonical logarithm on regular right-half-plane names

Close original samples are compared in their common signed rational
chart. The logarithm's rescaling law returns the comparison to the
original two data codes. The generic right-half-plane lift then gives
regularity, properness and an arbitrary late rational comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmNamed

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianLogGammaEulerCommonDenominator
  (commonReal commonImag common_sources common_size continuityRadius
    continuity_radius_from_distance displacement sizeBound)
open GaussianNameEquivalence (crossEquivalent cross_symm)
open GaussianNamedInverseRate (independentRate subst_independentRate)
open GaussianNamedRightHalfPlaneSigned (certificate denominator imagNumerator point realNumerator sign)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalL1 (raw_den_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalValueEquality (commonDen)
open GaussianRightHalfPlaneLogarithmRationalContinuity (local_guard widened_rate)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "d" => GaussianRightHalfPlaneLogarithm.data

def pointData (q : PTm n) : PTm n :=
  d (realNumerator q) (imagNumerator q) (denominator q) (sign q)

def rationalData : PR 1 := PTm.toPR (pointData (var 0) : PTm 1)

def coefficient (R K : PTm n) : PTm n :=
  GaussianRightHalfPlaneLogarithmRationalContinuity.gain K (sizeBound R R)

def gain : PR 2 := PTm.toPR (coefficient (var 0) (var 1) : PTm 2)

@[simp] theorem subst_pointData {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (pointData q) = pointData (Syn.subst σ q) := by simp [pointData]

theorem rational_data_at (q : PTm n) : Γ ⊢[PRAAx] ap1 rationalData q ≐ pointData q := by
  simpa only [rationalData, ap1, subst_pointData, Syn.subst_var, Matrix.cons_val_zero] using
    toPR_eq (Γ := Γ) (pointData (var 0) : PTm 1) ![q]

theorem gain_at (R K : PTm n) : Γ ⊢[PRAAx] ap2 gain R K ≐ coefficient R K := by
  simpa only [gain, ap2, coefficient, GaussianRightHalfPlaneLogarithmRationalContinuity.subst_gain,
    GaussianLogGammaEulerCommonDenominator.subst_sizeBound, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one] using toPR_eq (Γ := Γ) (coefficient (var 0) (var 1) : PTm 2) ![R,K]

private theorem denominator_congr (A B D E neg : PTm n) (h : Γ ⊢[PRAAx] D ≐ E) :
    Γ ⊢[PRAAx] d A B D neg ≐ d A B E neg := by
  simpa only [GaussianRightHalfPlaneLogarithm.subst_data, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (d (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![A,B,D,neg]) (σ' := ![A,B,E,neg]) (fun i => by
        fin_cases i
        exact .eqRefl _
        exact .eqRefl _
        exact h
        exact .eqRefl _)

theorem original_chart (q r R S K : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K) : Γ ⊢[PRAAx]
    crossEquivalent G G (d (commonReal q r) (commonImag q r) (commonDen q r) (sign q)) (pointData q) ⋏
      crossEquivalent G G (d (commonReal r q) (commonImag r q) (commonDen q r) (sign r)) (pointData r) := by
  have left := GaussianRightHalfPlaneLogarithmRescale.rescale (realNumerator q) (imagNumerator q)
    (denominator q) (sign q) (denominator r) hq.andE₁.andE₁ (raw_den_positive r)
  have right := GaussianRightHalfPlaneLogarithmRescale.rescale (realNumerator r) (imagNumerator r)
    (denominator r) (sign r) (denominator q) hr.andE₁.andE₁ (raw_den_positive q)
  have eq := denominator_congr (Γ := Γ) (commonReal q r) (commonImag q r) (denominator r*denominator q)
    (commonDen q r) (sign q) (mul_comm _ _)
  exact .andI (cross_data_congr G G _ _ _ _ eq (.eqRefl _) left) right

private theorem original_distance (x y E D : PTm n)
    (hx : Γ ⊢[PRAAx] le one (realNumerator x)) (hy : Γ ⊢[PRAAx] le one (realNumerator y))
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded (point x) (point y) E D) :
    Γ ⊢[PRAAx] distanceBounded x y E D := by
  have left := distance_radius_mono _ _ zero one zero D (le_refl one) hD (by ipra_le 0)
    (distance_symmetric _ _ _ _ (le_refl one) (GaussianNamedRightHalfPlaneSigned.point_distance_raw x hx))
  have right := distance_radius_mono _ _ zero one zero D (le_refl one) hD (by ipra_le 0)
    (GaussianNamedRightHalfPlaneSigned.point_distance_raw y hy)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD left h) right)

theorem original_variation (x y R K E D : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hD : Γ ⊢[PRAAx] le one D) (small : Γ ⊢[PRAAx] le (coefficient R K * E) D)
    (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) E D) :
    Γ ⊢[PRAAx] independentRate G G (pointData x) (pointData y) (coefficient R K * E) D := by
  let d₀ := commonDen y x
  let C := sizeBound R R
  let H := continuityRadius (displacement y x)
  let A := commonReal y x
  let B := commonImag y x
  let a := commonReal x y
  let b := commonImag x y
  have hxy := original_distance x y E D hx.andE₁.andE₁.andE₁.andE₁ hy.andE₁.andE₁.andE₁.andE₁ hD near
  have hK := GaussianDominantScalarOrder.factor_positive_left K (realNumerator x)
    (le_trans hx.andE₁.andE₁.andE₂ hx.andE₂.andE₁)
  have hs := common_sources y x R R K hy hx
  have hStep := continuity_radius_from_distance y x R R K E D hy hx hD hxy
  have admitted := GaussianRightHalfPlaneLogarithmIncrementMargin.admitted A B (sign y) a b (sign x) d₀ H K C
    hs.andE₁.andE₁ hs.andE₂.andE₁.andE₁ hStep.andE₁ hK hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₂
    (common_size y x R R K hy hx) (local_guard H E K C d₀ D hD hStep.andE₂ small)
  have rate := widened_rate A B (sign y) a b (sign x) d₀ H _ _ K C E D admitted hs.andE₂.andE₂.andE₁ hD hStep.andE₂
  have chart := original_chart y x R R K hy hx
  exact GaussianNamedRateTransport.transport G G G G _ _ _ _ _ _ hD rate
    (cross_symm _ _ _ _ chart.andE₂) (cross_symm _ _ _ _ chart.andE₁)

theorem variation (x y R K E D : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hD : Γ ⊢[PRAAx] le one D) (small : Γ ⊢[PRAAx] le (ap2 gain R K * E) D)
    (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) E D) :
    Γ ⊢[PRAAx] independentRate G G (ap1 rationalData x) (ap1 rationalData y) (ap2 gain R K * E) D := by
  have eq := congrMul (gain_at (Γ := Γ) R K) (.eqRefl E)
  have rate := original_variation x y R K E D hx hy hD (le_congr eq (.eqRefl _) small) near
  let φ : Fm PTm 4 := independentRate G G (var 0) (var 1) (var 2) (var 3)
  have result := Prf.eqSubst (Γ := Γ) (Ax := PRAAx) φ
    ![pointData x,pointData y,coefficient R K*E,D] ![ap1 rationalData x,ap1 rationalData y,ap2 gain R K*E,D]
    (fun i => by
      fin_cases i
      exact (rational_data_at x).eqSymm
      exact (rational_data_at y).eqSymm
      exact eq.eqSymm
      exact .eqRefl D)
    (by simpa only [φ, subst_independentRate, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using rate)
  simpa only [φ, subst_independentRate, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using result

def rationalMap : GaussianNamedRightHalfPlaneLift.RationalMap where
  evaluator := G
  rationalData := rationalData
  gain := gain
  variation := variation

abbrev source (f : PR 2) (x M R : PTm n) : Fm PTm n := GaussianNamedRightHalfPlaneLift.source f x M R
abbrev nameF (f : PR 2) : PR 2 := GaussianNamedRightHalfPlaneLift.nameF rationalMap f
abbrev data (x M R : PTm n) : PTm n := GaussianNamedRightHalfPlaneLift.data x M R
abbrev clock (p M R : PTm n) : PTm n := GaussianNamedRightHalfPlaneLift.clock rationalMap p M R

theorem name_regular (f : PR 2) (x M R : PTm n) (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data x M R) :=
  GaussianNamedRightHalfPlaneLift.name_regular rationalMap f x M R h

theorem proper (f g : PR 2) (x y M R : PTm n) (hx : Γ ⊢[PRAAx] source f x M R)
    (hy : Γ ⊢[PRAAx] source g y M R) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x M R) (data y M R) :=
  GaussianNamedRightHalfPlaneLift.proper rationalMap f g x y M R hx hy h

theorem late_rational_rate (f : PR 2) (s k x M R : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) (hk : Γ ⊢[PRAAx] le (clock s M R) k) :
    Γ ⊢[PRAAx] independentRate (nameF f) G (data x M R) (pointData (ap2 f k x)) one (unit s) := by
  let Z := data x M R
  let Y := ap2 f k x
  let φ := independentRate (nameF f) G (Syn.shift Z) (var 0) (Syn.shift one) (Syn.shift (unit s))
  have raw : Γ ⊢[PRAAx] independentRate (nameF f) G Z (ap1 rationalData Y) one (unit s) :=
    GaussianNamedRightHalfPlaneLift.frozen_rate rationalMap f s k x M R h hk
  simpa only [φ, subst_independentRate, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, Z, Y] using
    Prf.eqSubst1 φ (rational_data_at Y)
      (by simpa only [φ, subst_independentRate, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using raw)

theorem actual_named_right_half_plane_logarithm_regular_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular f _ _ _ Prf.hyp0))

theorem actual_named_right_half_plane_logarithm_late_rational_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source f (var 0) (var 1) (var 2) ⟶ le (clock (var 3) (var 1) (var 2)) (var 4) ⟶
        independentRate (nameF f) G (data (var 0) (var 1) (var 2)) (pointData (ap2 f (var 4) (var 0)))
          one (unit (var 3))) :=
  closeUniv 5 (.impI (.impI (late_rational_rate f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmNamed
