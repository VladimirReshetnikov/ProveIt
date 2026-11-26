import IPRADerivations.Analysis.Stirling.Binet.Laplace.Rectangles.GaussianBinetLaplaceWeightedGridProduct

/-!
# Sufficient budgets for a dyadic error on the rectangle row side

The inner mesh and later row clock can be chosen independently of
the outer time mesh and of the encodings of its rational tags.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceRectangleRowBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceWeightedGridProduct (baseCost rowBudget)
open GaussianBinetWeightedExponentialRowRate (gain)
open GaussianBinetWeightedExponentialUniform (readBudget)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def meshCost (T : PTm n) : PTm n := T*two*gain T
def clockCost (T : PTm n) : PTm n := T*(baseCost T+two*(gain T+num 8))

theorem row_budget (p q M T : PTm n)
    (hm : Γ ⊢[PRAAx] le (meshCost T*unit p) M)
    (hq : Γ ⊢[PRAAx] le (clockCost T*unit p) (unit q)) :
    Γ ⊢[PRAAx] le ((T*rowBudget q M T)*unit p) (two*(M*unit q)) := by
  have first := mul_le_mul_right (unit q) hm
  have second := mul_le_mul_right M hq
  exact le_congr (by dsimp only [rowBudget,readBudget,meshCost,clockCost]; ipra_ring)
    (by ipra_ring) (add_le_add₂ first second)

theorem dyadic_error (p q M T x y : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hm : Γ ⊢[PRAAx] le (meshCost T*unit p) M)
    (hq : Γ ⊢[PRAAx] le (clockCost T*unit p) (unit q))
    (h : Γ ⊢[PRAAx] distanceBounded x y (T*rowBudget q M T) (M*unit q)) :
    Γ ⊢[PRAAx] distanceBounded x y two (unit p) :=
  GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ hM (unit_positive q)) (unit_positive p) (row_budget p q M T hm hq) h

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceRectangleRowBudget
