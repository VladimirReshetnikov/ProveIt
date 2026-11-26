import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicClientIndependence
import IPRADerivations.Analysis.Euler.Logarithms.LowerBounds.GaussianEulerLogarithmicLowerCutoffBudget

/-!
# The actual logarithmic lower tail at an arbitrary containing top guard

The lower-tail source is proved at top one. Its original interval and
evaluator are compared with the client using an arbitrary top T>=1.
The exact factorial coefficient and only the requested observation error
survive a finite rational gap. No bound on a transported output is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerGuardBound

open_ipra
open GaussianEulerLogarithmicLowerRootRows (panelDegree intervalDen)
open GaussianEulerLogarithmicNamedLowerBound (source leading numerator denominator)
open GaussianEulerLogarithmicIntervalName (nameF)
open GaussianGammaCompactCutoffGeometry (lowerWidth ratio lower_endpoint)
open GaussianGammaIntegralCutoffs (height eta_den_positive)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (j z R B k l A T : PTm n) : PTm n := GaussianEulerLogarithmicIntervalName.data
  j z R B one (lowerWidth k l (panelDegree A)) (intervalDen l A R) T
def point (p j z R B k l A T : PTm n) : PTm n := ap2 nameF p (data j z R B k l A T)

theorem interval_source (z R B k l A T : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hkl : Γ ⊢[PRAAx] le k l) (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx]
    GaussianEulerCompactAdditivity.intervalSource z R B one (lowerWidth k l (panelDegree A)) (intervalDen l A R) T := by
  let E := intervalDen l A R
  let D := panelDegree A
  have ratioBound : Γ ⊢[PRAAx] le (ratio k l D) E :=
    le_congr (one_mul _) ((mul_comm _ _).eqTrans
      (GaussianGammaCompactCutoffGeometry.eta_den_refinement k l D R hkl).eqSymm)
      (mul_le_mul_right (ratio k l D) (eta_den_positive k D R))
  have endpoint : Γ ⊢[PRAAx] le (one+lowerWidth k l D) (E*one) :=
    le_congr (lower_endpoint k l D).eqSymm (by ipra_ring) ratioBound
  have top : Γ ⊢[PRAAx] le (E*one) (E*T) :=
    le_congr (by ipra_ring) (mul_comm _ _) (mul_le_mul_right E hT)
  exact .andI (.andI h.andE₂.andE₁.andE₁ (.andI (eta_den_positive l D R) h.andE₂.andE₁.andE₂))
    (.andI (le_refl one) (le_trans endpoint top))

theorem original_client_cross (j z R B k l A T : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hkl : Γ ⊢[PRAAx] le k l) (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent nameF nameF (data j z R B k l A T)
      (GaussianEulerLogarithmicNamedLowerBound.data j z R B k l A) :=
  GaussianEulerLogarithmicClientIndependence.original_independence j z R R B one (lowerWidth k l (panelDegree A))
    (intervalDen l A R) (intervalDen l A R) T (intervalDen l A R) one
    (.andI (GaussianEulerLogarithmicClientIntervalName.canonical_source _ _ _ _ _ _ _ (interval_source z R B k l A T h hkl hT))
      (GaussianEulerLogarithmicClientIntervalName.canonical_source _ _ _ _ _ _ _ (interval_source z R B k l A one h hkl (le_refl one))))

theorem original_slack (p q j z R B k l A T : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hkl : Γ ⊢[PRAAx] le k l) (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (point p j z R B k l A T) (numerator p j k A R) (denominator p k A R) two q := by
  let P := unit p
  let Q := unit q
  let H := unit (height k (panelDegree A) R)
  let F := leading j A
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hh := unit_positive (Γ := Γ) (height k (panelDegree A) R)
  have near := GaussianNameEquivalence.cross_at _ _ _ _ p q (original_client_cross j z R B k l A T h hkl hT)
  have old : Γ ⊢[PRAAx] bounded (GaussianEulerLogarithmicNamedLowerBound.point q j z R B k l A) (F*Q+H) (H*Q) :=
    GaussianEulerLogarithmicNamedLowerBound.original_named_bound q j z R B k l A h hkl
  have joined := GaussianReconstructionRoots.norm_from_distance _ _ (P+Q) (P*Q) (F*Q+H) (H*Q)
    (positive_product _ _ hp hq) (positive_product _ _ hh hq) near old
  exact bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hp hq) (positive_product _ _ hh hq))
    (positive_product _ _ (positive_product _ _ hh hp) hq)
    (le_of_eq_add (d := zero) (by unfold numerator denominator; dsimp only [P,Q,H,F]; unfold unit; ipra_ring)) joined

theorem original_named_bound (p j z R B k l A T : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hkl : Γ ⊢[PRAAx] le k l) (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx]
    bounded (point p j z R B k l A T) (numerator p j k A R) (denominator p k A R) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ two
    (positive_product _ _ (unit_positive _) (unit_positive p)) (original_slack p _ j z R B k l A T h hkl hT)

theorem original_cutoff_tail_bound (p j z R B r k l A T : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hclock : Γ ⊢[PRAAx] le (GaussianEulerLogarithmicLowerCutoffBudget.clock r j A) k)
    (hkl : Γ ⊢[PRAAx] le k l) (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx]
    bounded (point p j z R B k l A T) (unit p+unit (r+num 6)) (unit (r+num 6)*unit p) := by
  have old := original_named_bound p j z R B k l A T h hkl hT
  have budget := GaussianEulerLogarithmicLowerCutoffBudget.original_coefficient_budget r j k A R hclock
  apply bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive p)) (positive_product _ _ (unit_positive _) (unit_positive p)) _ old
  unfold numerator
  ipra_le (Groth.ι (Q.mk Γ (unit p)))^2*sl budget

theorem actual_logarithmic_lower_tail_at_larger_top_guard_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 2) (var 3) (var 4) (var 7) ⋏ (le (var 5) (var 6) ⋏ le one (var 8))) ⟶
      bounded (point (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (numerator (var 0) (var 1) (var 5) (var 7) (var 3)) (denominator (var 0) (var 5) (var 7) (var 3))) :=
  closeUniv 9 (.impI (original_named_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicLowerGuardBound
