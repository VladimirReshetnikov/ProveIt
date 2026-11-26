import IPRADerivations.Analysis.Stirling.Binet.Laplace.Rectangles.GaussianBinetLaplaceWeightedGridRectangle
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Rectangles.GaussianBinetLaplaceRectangleSchedule

/-!
# Join the original Binet difference and the weighted-resolvent comparison

Both finite estimates use the same rectangle and one clock. The time
mesh is a common refinement of the original two compact names.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceRectangleJoin

open_ipra
open GaussianBinetFirstFormulaPinning (laplaceStepData)
open GaussianBinetLaplaceDifferenceGrid (gridCount gridValue at_common_grid)
open GaussianBinetLaplaceDifferencePrefix (shifted_source)
open GaussianBinetLaplaceOrderedPrefixes (width)
open GaussianBinetLaplaceRectangleRowBudget (clockCost dyadic_error)
open GaussianBinetLaplaceRectangleSchedule (cutoff horizon clock unitMesh extra timeMesh
  cutoff_bounds clock_bounds unit_mesh_bounds time_mesh_bounds horizon_eq reciprocal_margin)
open GaussianBinetExponentialRectangleEvaluation (rectangle original_resolvent_rate)
open GaussianBinetExponentialRectangle (outerBody data)
open GaussianBinetLogCellGrid (requiredMesh)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (precision)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qmul)
open GaussianRationalMetric (distanceBounded qnegative)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem rectangle_horizon_congr (q X Y D sign R T U N M : PTm n)
    (h : Γ ⊢[PRAAx] T ≐ U) : Γ ⊢[PRAAx] rectangle q X Y D sign R T N M ≐ rectangle q X Y D sign R U N M := by
  let z := qnegative (argument X Y D sign)
  simpa only [rectangle, z, GaussianRationalHorner.subst_qmul, GaussianPositiveRationalLogarithm.subst_fraction,
    GaussianRationalFiniteSum.subst_sum, GaussianBinetExponentialRectangle.subst_data, PTm.subst_mul,
    Syn.inst_zero, Syn.subst_inst_shift, Syn.subst_var] using
    Prf.eqCongr1 (qmul (fraction (var 0) (Syn.shift N))
      (sum outerBody (Syn.shift N) (data (Syn.shift q) (Syn.shift z) (Syn.shift R*var 0)
        (var 0) (Syn.shift N) (Syn.shift M)))) h

local notation "J" => GaussianBinetLaplaceImproperName.nameF
local notation "U" => GaussianBinetStirlingUnitDifference.nameF
local notation "ud" => GaussianBinetStirlingUnitDifference.data

def comparisonCost (X Y D sign : PTm n) : PTm n :=
  num 16+two+(two+GaussianBinetWeightedResolvent.budget X Y D sign)

ipra_subst comparisonCost [two]

theorem original_observation (p X Y D sign : PTm n) (h : Γ ⊢[PRAAx] source X D sign) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 (GaussianNamedDifference.nameF J J) p (laplaceStepData X Y D sign))
      (ap2 U p (ud X Y D sign)) (comparisonCost X Y D sign) (unit p) := by
  let R := radius X Y
  let S := radius (X+D) Y
  let L := cutoff p D
  let T := horizon p D
  let r := clock p X Y D
  let M := unitMesh p X Y D
  let N := timeMesh p X Y D
  let q := r+N
  have hR := source_of_right_half_plane X Y D sign h
  have hS := source_of_right_half_plane (X+D) Y D sign (shifted_source X D sign h)
  have a := cutoff_bounds (Γ := Γ) p D
  have b := clock_bounds (Γ := Γ) p X Y D
  have c := unit_mesh_bounds (Γ := Γ) p X Y D
  have d := time_mesh_bounds (Γ := Γ) p X Y D
  have hm' : Γ ⊢[PRAAx] le one M := le_trans (unit_positive p) c.andE₁
  have hq : Γ ⊢[PRAAx] le (precision p T) q := le_trans b.andE₂.andE₁ (le_add_right r N)
  have timeBudget : Γ ⊢[PRAAx] le (clockCost T*unit p) (unit q) :=
    le_trans b.andE₂.andE₂.andE₂ (GaussianExponentialReference.unit_monotone (le_add_right r N))
  have row := GaussianBinetLaplaceWeightedGridRectangle.quadrature_distance q N M X Y D sign R S T hR hS d.andE₂.andE₁ hm'
  have close := dyadic_error p q M T (gridValue q N X Y D sign L) (rectangle q X Y D sign R T N M)
    hm' c.andE₂.andE₂ timeBudget row
  have rect := rectangle_horizon_congr (Γ := Γ) q X Y D sign R T (D*L) N M (horizon_eq p D)
  have first := at_common_grid p q X Y D sign L (extra p X Y D) h a.andE₁ d.andE₁ a.andE₂.andE₁ hq
  have last := original_resolvent_rate p r X Y D sign R D L N M hR (reciprocal_margin X D h.andE₁.andE₁)
    c.andE₁ c.andE₂.andE₁ b.andE₁ d.andE₂.andE₂.andE₁ d.andE₂.andE₂.andE₂ a.andE₂.andE₂ b.andE₂.andE₂.andE₁
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first
      (distance_congr (.eqRefl _) rect (.eqRefl _) (.eqRefl _) close)) last

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceRectangleJoin
