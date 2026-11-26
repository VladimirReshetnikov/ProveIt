import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaCoefficientObservationPolynomials
import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaUnitCoefficientMass
import IPRADerivations.Analysis.Names.GaussianShrinkingGridValueRecovery

/-!
# Original coefficient comparison on a computed shrinking Gamma grid

At H=2^(t+e), the original full polynomials are sampled at precision
H^(e+1)+t. Actual original C7 overlap and the uniform coefficient mass
discharge every finite-grid premise of coefficient recovery. The SAME
original coefficient names at this computed precision differ by a
computed constant times 2^(-t), even at distinct positive radii.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaShrinkingGridCoefficientComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCoefficientObservationPolynomials (polynomial degree)
open GaussianRationalHorner (evaluate ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalFiniteGridIdentity (nativePoint)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianShrinkingGridValueRecovery (query valuesClose)
open GaussianLagrangeCoefficientSensitivity (gain)
open GaussianGammaCanonicalExponent (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def mesh (t e : PTm n) : PTm n := unit (t+e)
def precision (t e : PTm n) : PTm n := pw (mesh t e) (succ e)+t
def budget (R S e : PTm n) : PTm n := two*gain e e*
  (two+(GaussianGammaUnitCoefficientMass.budget R+GaussianGammaUnitCoefficientMass.budget S)*pw e (succ e))
@[simp] theorem subst_mesh {l : ℕ} (σ : Fin n → PTm l) (t e : PTm n) :
    Syn.subst σ (mesh t e) = mesh (Syn.subst σ t) (Syn.subst σ e) := by simp [mesh]
@[simp] theorem subst_precision {l : ℕ} (σ : Fin n → PTm l) (t e : PTm n) :
    Syn.subst σ (precision t e) = precision (Syn.subst σ t) (Syn.subst σ e) := by simp [precision]
@[simp] theorem subst_budget {l : ℕ} (σ : Fin n → PTm l) (R S e : PTm n) :
    Syn.subst σ (budget R S e) = budget (Syn.subst σ R) (Syn.subst σ S) (Syn.subst σ e) := by simp [budget]

theorem mesh_positive (t e : PTm n) : Γ ⊢[PRAAx] le one (mesh t e) := unit_positive _
theorem mesh_degree (t e : PTm n) : Γ ⊢[PRAAx] le e (mesh t e) :=
  le_trans (le_trans (le_add_left e t) (le_succ_self _)) (RationalClosure.succ_le_two_pow _)
theorem mesh_later (t e : PTm n) : Γ ⊢[PRAAx] le (unit t) (mesh t e) :=
  GaussianFactorBudget.power_monotone_length two t (t+e) (le_succ_self one) (le_add_right _ _)
theorem precision_later (t e : PTm n) : Γ ⊢[PRAAx] le t (precision t e) := le_add_left _ _
theorem precision_unit (t e : PTm n) : Γ ⊢[PRAAx] le (pw (mesh t e) (succ e)) (unit (precision t e)) :=
  le_trans (le_trans (le_add_right _ _) (le_succ_self _)) (RationalClosure.succ_le_two_pow _)

theorem query_code (H s : PTm n) (hH : Γ ⊢[PRAAx] le one H) : Γ ⊢[PRAAx]
    query H s ≐ ofGaussian (nativePoint s) H :=
  (GaussianDominantPairAlgebra.radius_multiply one H s one hH (le_refl one)).eqTrans
    (GaussianDominantPairAlgebra.radius_congr (by ipra_ring) (by ipra_ring))
theorem grid_source (s R H : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hH : Γ ⊢[PRAAx] le one H)
    (hs : Γ ⊢[PRAAx] le s H) : Γ ⊢[PRAAx] source (nativePoint s) R H := by
  have radius : Γ ⊢[PRAAx] le s (R*H) :=
    le_trans hs (le_congr (show Γ ⊢[PRAAx] one*H ≐ H by ipra_ring) (.eqRefl _) (mul_le_mul_right H hR))
  exact .andI hR (.andI hH
    (le_congr (GaussianDominantPairAlgebra.radius_numerator_norm s).eqSymm (.eqRefl _) (sq_le_sq radius)))

theorem grid_point_error (t R S e s : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hS : Γ ⊢[PRAAx] le one S)
    (hs : Γ ⊢[PRAAx] le s e) : Γ ⊢[PRAAx]
    distanceBounded (evaluate (polynomial (precision t e) R e) (query (mesh t e) s))
      (evaluate (polynomial (precision t e) S e) (query (mesh t e) s)) two (mesh t e*pw (mesh t e) e) := by
  have hH := mesh_positive (Γ := Γ) t e
  have bound := le_trans hs (mesh_degree (Γ := Γ) t e)
  have original := GaussianGammaCoefficientObservationPolynomials.original_value_overlap (precision t e) (precision t e) R S e
    (nativePoint s) (mesh t e) (grid_source s R _ hR hH bound) (grid_source s S _ hS hH bound)
  have old := distance_congr (Γ := Γ)
    (GaussianRationalMonicReduction.evaluate_congr (.eqRefl _) (query_code _ s hH).eqSymm)
    (GaussianRationalMonicReduction.evaluate_congr (.eqRefl _) (query_code _ s hH).eqSymm)
    (.eqRefl _) (.eqRefl _) original
  have clear : Γ ⊢[PRAAx] pw (mesh t e) (succ e)*(two*unit (precision t e)) ≐
      (unit (precision t e)+unit (precision t e))*(mesh t e*pw (mesh t e) e) :=
    (congrMul (pw_succ (mesh t e) e) (.eqRefl _)).eqTrans (by ipra_ring)
  have rad : Γ ⊢[PRAAx] le ((unit (precision t e)+unit (precision t e))*(mesh t e*pw (mesh t e) e))
      (two*(unit (precision t e)*unit (precision t e))) :=
    le_congr clear (by ipra_ring) (mul_le_mul_right (two*unit (precision t e)) (precision_unit t e))
  exact distance_radius_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive _) (unit_positive _))
    (GaussianRationalHorner.positive_product _ _ hH (GaussianFactorBudget.power_positive _ _ hH)) rad old

theorem original_grid_errors (t R S e : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    valuesClose (polynomial (precision t e) R e) (polynomial (precision t e) S e) e (mesh t e) two (mesh t e) := by
  have rs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have ss : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift S) := by simpa [Fm.shift,Syn.shift] using hS.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_mesh,subst_precision,GaussianGammaCoefficientObservationPolynomials.subst_polynomial,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      grid_point_error (Syn.shift t) (Syn.shift R) (Syn.shift S) (Syn.shift e) (var 0) rs.wk ss.wk Prf.hyp0

theorem original_coefficient_comparison (t R S e : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaRadiusCoefficientName.sample (precision t e) R e)
      (GaussianGammaRadiusCoefficientName.sample (precision t e) S e) (budget R S e) (mesh t e) := by
  have hH := mesh_positive (Γ := Γ) t e
  have finite := GaussianShrinkingGridValueRecovery.original_coefficient_error
    (polynomial (precision t e) R e) (polynomial (precision t e) S e)
    (degree (precision t e) R e) (degree (precision t e) S e) e (mesh t e)
    (GaussianGammaUnitCoefficientMass.budget R) (GaussianGammaUnitCoefficientMass.budget S) two (mesh t e)
    (GaussianGammaCoefficientObservationPolynomials.polynomial_length _ _ _)
    (GaussianGammaCoefficientObservationPolynomials.polynomial_length _ _ _)
    (GaussianGammaCoefficientObservationPolynomials.original_degree_guard _ _ _)
    (GaussianGammaCoefficientObservationPolynomials.original_degree_guard _ _ _) hH (mesh_degree t e) hH
    (GaussianGammaUnitCoefficientMass.original_coefficient_mass _ _ _ _ hR)
    (GaussianGammaUnitCoefficientMass.original_coefficient_mass _ _ _ _ hS) (original_grid_errors t R S e hR hS)
  have actual := distance_congr
    (GaussianGammaCoefficientObservationPolynomials.original_coefficient_binding _ _ _).eqSymm
    (GaussianGammaCoefficientObservationPolynomials.original_coefficient_binding _ _ _).eqSymm (.eqRefl _) (.eqRefl _) finite
  exact GaussianMonicResidualRadius.bounded_cancel _ _ _ (mesh t e) hH hH
    (GaussianRationalReciprocal.bound_congr (.eqRefl _) (by unfold budget GaussianShrinkingGridValueRecovery.errorNumerator; ipra_ring)
      (.eqRefl _) actual)

theorem original_dyadic_coefficient_comparison (t R S e : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaRadiusCoefficientName.sample (precision t e) R e)
      (GaussianGammaRadiusCoefficientName.sample (precision t e) S e) (budget R S e) (unit t) :=
  distance_radius_mono _ _ _ _ _ _ (mesh_positive t e) (unit_positive t)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (budget R S e) (mesh_later t e)))
      (original_coefficient_comparison t R S e hR hS)

theorem original_computed_grid_Gamma_coefficient_radius_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le one (var 2) ⟶ distanceBounded
      (GaussianGammaRadiusCoefficientName.sample (precision (var 0) (var 3)) (var 1) (var 3))
      (GaussianGammaRadiusCoefficientName.sample (precision (var 0) (var 3)) (var 2) (var 3))
        (budget (var 1) (var 2) (var 3)) (unit (var 0))) :=
  closeUniv 4 (.impI (.impI (original_dyadic_coefficient_comparison _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaShrinkingGridCoefficientComparison
