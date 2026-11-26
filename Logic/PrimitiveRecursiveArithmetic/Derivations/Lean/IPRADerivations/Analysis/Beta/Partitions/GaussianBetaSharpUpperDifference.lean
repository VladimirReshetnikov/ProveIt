import IPRADerivations.Analysis.Beta.Tails.GaussianBetaEulerUpperDifferenceGrid
import IPRADerivations.Analysis.Inequalities.WeightedComparison.GaussianWeightedHalfDecayEndpoint
import IPRADerivations.Analysis.Beta.Partitions.GaussianBetaSharpPartition

/-!
# The literal sharp upper interval [N/2,N] on its original shared grid

The degree is the exact sharp schedule. Its actual quarter-degree
decay observation pays the entire endpoint term with one D_R; the
original weighted beta--Euler grid difference retains the explicit
mesh and ordinary observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaSharpUpperDifference

open_ipra
open GaussianEulerSharpDegreeSchedule (degree height degree_positive degree_is_four_height height_positive)
open GaussianBetaSharpPartition (halfPoint supportTailWidth halfDen even_denominator half_boundary_order half_point_decay_sample)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianWeightedHalfDecayEndpoint (coefficient meshNumerator meshDenominator)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianCompactRiemannName (quadrature)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def endpointClock (t R : PTm n) : PTm n := GaussianFastValueCut.exponent (num 8*coefficient R) (t+num 4)
def start (t k A R : PTm n) : PTm n := halfPoint k A R (degree t R)
def width (t k A R : PTm n) : PTm n := supportTailWidth k A R (degree t R)
def count (t k A S R : PTm n) : PTm n := width t k A R*S
def halfNumerator (t p k A S R : PTm n) : PTm n :=
  coefficient R*meshNumerator p (endpointClock t R) (count t k A S R) (width t k A R) (etaDen k A R)*unit (t+num 3)+
    meshDenominator p (endpointClock t R) (count t k A S R) (etaDen k A R)
def halfDenominator (t p k A S R : PTm n) : PTm n :=
  meshDenominator p (endpointClock t R) (count t k A S R) (etaDen k A R)*unit (t+num 3)
def numerator (t p k A S R : PTm n) : PTm n :=
  (width t k A R*GaussianBetaEulerTailDifferencePointwise.referenceError R)*halfDenominator t p k A S R+
    halfNumerator t p k A S R*(etaDen k A R*unit p)
def denominator (t p k A S R : PTm n) : PTm n := (etaDen k A R*unit p)*halfDenominator t p k A S R
def beta (t p k A S z R B : PTm n) : PTm n := quadrature GaussianBetaKernelGridComparison.evaluatorF p (count t k A S R)
  (start t k A R) (width t k A R) (etaDen k A R) (GaussianBetaKernelGridComparison.sampleDataBeta z B (degree t R))
def euler (t p k A S z R B : PTm n) : PTm n := quadrature GaussianEulerIntegrandName.evaluatorF p (count t k A S R)
  (start t k A R) (width t k A R) (etaDen k A R) (GaussianEulerIntegrandName.fixedData z B)

theorem degree_two_lower (t R : PTm n) : Γ ⊢[PRAAx] le two (degree t R) := by
  have grow : Γ ⊢[PRAAx] le (num 4) (degree t R) := le_congr (one_mul _) (by
    exact (mul_comm _ _).eqTrans (degree_is_four_height t R).eqSymm)
      (mul_le_mul_right (num 4) (height_positive t R))
  exact le_trans (le_of_eq_add (d := two) (by ipra_ring)) grow

theorem width_is_start (t k A R : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    width t k A R ≐ start t k A R := by
  have twice : Γ ⊢[PRAAx] etaDen k A R*degree t R ≐ start t k A R+start t k A R := by
    apply deriveNat
    have eq := natEq (even_denominator (Γ := Γ) k A R hA)
    dsimp only [start,halfPoint]
    ipra_simps
    rw [eq]
    ring
  exact (congrMonus twice (.eqRefl _)).eqTrans (add_monus' _ _)

theorem geometry (t k A R : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    le one (width t k A R) ⋏ (le one (start t k A R) ⋏
      (le (etaDen k A R) (start t k A R) ⋏ start t k A R+width t k A R ≐ etaDen k A R*degree t R)) := by
  have bounds := half_boundary_order k A R (degree t R) hA (degree_two_lower t R)
  have ha := le_trans (eta_den_positive k A R) bounds.andE₁
  exact .andI (le_congr (.eqRefl _) (width_is_start t k A R hA).eqSymm ha)
    (.andI ha (.andI bounds.andE₁ (eq_add_of_le bounds.andE₂).eqSymm))

theorem endpoint_clock_budget (t R : PTm n) : Γ ⊢[PRAAx]
    le (num 8*coefficient R*unit (t+num 4)) (unit (endpointClock t R)) := GaussianFastValueCut.query_budget _ _

theorem original_scaled_half_bound (t p k A S R : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    bounded (qmul (radiusPoint (majorant R) one)
      (quadrature GaussianEulerCompactUpperTail.halfEvaluator p (count t k A S R) (start t k A R) (width t k A R) (etaDen k A R) zero))
      (halfNumerator t p k A S R) (halfDenominator t p k A S R) := by
  let q := endpointClock t R
  let M := count t k A S R
  let C := width t k A R
  let E := etaDen k A R
  let X := unit q+two*coefficient R*unit (t+num 4)
  let Y := unit (t+num 4)*unit q
  have geo := geometry t k A R hA
  have hm : Γ ⊢[PRAAx] le one M := positive_product _ _ geo.andE₁ hS
  have he := eta_den_positive (Γ := Γ) k A R
  have hy : Γ ⊢[PRAAx] le one Y := positive_product _ _ (unit_positive _) (unit_positive q)
  have step : Γ ⊢[PRAAx] le C ((two*E)*M) := le_congr (one_mul C) (by dsimp only [M,count]; ipra_ring)
    (mul_le_mul_right C (positive_product _ _ (positive_product _ _ (le_succ_self one) he) hS))
  have same := GaussianRationalSyntheticDivision.qmul_congr (.eqRefl (radiusPoint (coefficient R) one))
    (half_point_decay_sample q k A R (degree t R) hA)
  have hStart : Γ ⊢[PRAAx] bounded (qmul (radiusPoint (coefficient R) one)
      (GaussianEulerDecayMesh.observation (start t k A R) (two*E) q)) X Y :=
    bound_congr same.eqSymm (.eqRefl _) (.eqRefl _) (GaussianEulerSharpDegreeSchedule.original_weighted_decay_bound t R q)
  have raw := GaussianWeightedHalfDecayEndpoint.original_scaled_half_decay_bound p q M (start t k A R) C E R X Y
    geo.andE₂.andE₁ hm geo.andE₁ he step hy hStart
  have hd := GaussianWeightedHalfDecayEndpoint.mesh_denominator_positive p q M E hm he
  have next : Γ ⊢[PRAAx] unit (t+num 4) ≐ two*unit (t+num 3) :=
    ((congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] t+num 4 ≐ ConciseIPRA.PTm.succ (t+num 3)) (.eqRefl two)).eqTrans
      (pw_succ two (t+num 3))).eqTrans (mul_comm _ _)
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hd (positive_product _ _ hy (unit_positive q)))
    (positive_product _ _ hd (unit_positive _)) _ raw
  dsimp only [halfNumerator,halfDenominator,GaussianWeightedHalfDecayEndpoint.numerator,GaussianWeightedHalfDecayEndpoint.denominator,X,Y,q,M,C,E]
  have eq := natEq next
  ipra_le (𝔞(meshDenominator p (endpointClock t R) (count t k A S R) (etaDen k A R))*
      𝔞(meshDenominator p (endpointClock t R) (count t k A S R) (etaDen k A R))*𝔞(unit (t+num 3))*𝔞(unit (endpointClock t R)))*sl (endpoint_clock_budget t R) using
    rw [eq]
    ring

theorem original_upper_difference (t p k A S z R B : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerCoefficients.source z R B)
    (hA : Γ ⊢[PRAAx] le one A) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    distanceBounded (beta t p k A S z R B) (euler t p k A S z R B)
      (numerator t p k A S R) (denominator t p k A S R) := by
  have geo := geometry t k A R hA
  have hm := positive_product (Γ := Γ) _ _ geo.andE₁ hS
  have he := eta_den_positive (Γ := Γ) k A R
  have hd := GaussianWeightedHalfDecayEndpoint.mesh_denominator_positive p (endpointClock t R) (count t k A S R) (etaDen k A R) hm he
  exact GaussianBetaEulerUpperDifferenceGrid.original_grid_bound_from_scaled_half p (count t k A S R) (start t k A R)
    (width t k A R) (etaDen k A R) z R B (degree t R) (halfNumerator t p k A S R) (halfDenominator t p k A S R)
    hm he geo.andE₂.andE₂.andE₁ h (degree_positive t R) (le_congr (.eqRefl _) geo.andE₂.andE₂.andE₂ (le_refl _))
    (positive_product _ _ hd (unit_positive _)) (original_scaled_half_bound t p k A S R hA hS)

theorem original_exact_sharp_upper_beta_Euler_grid_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((GaussianEulerUpperPowerCoefficients.source (var 5) (var 6) (var 7) ⋏ (le one (var 3) ⋏ le one (var 4))) ⟶
      distanceBounded (beta (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (euler (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 6)) (denominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 6))) :=
  closeUniv 8 (.impI (original_upper_difference _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaSharpUpperDifference
