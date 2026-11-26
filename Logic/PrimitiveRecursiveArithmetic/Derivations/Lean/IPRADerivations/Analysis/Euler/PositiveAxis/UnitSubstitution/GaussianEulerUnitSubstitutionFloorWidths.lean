import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionFloorCuts
import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalTiltedFloorWidth

/-!
# Source-only adjacent widths of the actual original unit chart cuts

The genuine compact source discharges all nonnegativity and floor-order
guards. Only one adjacent tilt increment appears in the returned scalar
width radius; there is no factor depending on the number of nodes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionFloorWidths

open_ipra
open GaussianEulerUnitSubstitutionFloorCuts (cut source node node_below)
open GaussianEulerUnitSubstitutionTiltedNodes (reverseNode correctedNode)
open GaussianEulerUnitDecayInput (clock)
open RationalNonnegativeFloor (index)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (fraction)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem index_congr {q r M : PTm n} (e : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] index q M ≐ index r M := by
  simpa using Prf.eqCongr1 (index (var 0) (Syn.shift M)) e

theorem original_width_error (i k N a C E T M : PTm n) (hs : Γ ⊢[PRAAx] source k N a C E T M)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (fraction (monus (cut (succ i) k N a C E T M) (cut i k N a C E T M)) M)
      (RationalArithmetic.add (reverseNode (succ i) (clock k E T) N a C E)
        (RationalArithmetic.negative (reverseNode i (clock k E T) N a C E)))
      (two*M+two*unit (clock k E T)) (M*unit (clock k E T)) := by
  have cs := GaussianEulerUnitSubstitutionFloorCuts.original_cut_source i k N a C E T M hs
  have hM : Γ ⊢[PRAAx] le one M := le_trans cs.andE₁.andE₁ (le_of_lt cs.andE₁.andE₂)
  have eqHere : Γ ⊢[PRAAx] cut i k N a C E T M ≐ index (correctedNode i (clock k E T) N a C E) M :=
    index_congr (node_below i k N a C E T (le_of_lt hi))
  have eqNext : Γ ⊢[PRAAx] cut (succ i) k N a C E T M ≐ index (correctedNode (succ i) (clock k E T) N a C E) M :=
    index_congr (node_below (succ i) k N a C E T hi)
  have ha := RationalArgmin.rationalLE_congr (.eqRefl _)
    (node_below i k N a C E T (le_of_lt hi))
    (GaussianEulerUnitSubstitutionFloorCuts.node_nonnegative i k N a C E T M hs)
  have hb := RationalArgmin.rationalLE_congr (.eqRefl _)
    (node_below (succ i) k N a C E T hi)
    (GaussianEulerUnitSubstitutionFloorCuts.node_nonnegative (succ i) k N a C E T M hs)
  have ordered := le_congr eqHere eqNext (GaussianEulerUnitSubstitutionFloorCuts.original_cut_step i k N a C E T M hs)
  have raw := RationalTiltedFloorWidth.original_width_error
    (reverseNode i (clock k E T) N a C E) (reverseNode (succ i) (clock k E T) N a C E)
    i two (unit (clock k E T)) M (unit_positive _) hM ha hb ordered
  have widths : Γ ⊢[PRAAx]
      fraction (monus (cut (succ i) k N a C E T M) (cut i k N a C E T M)) M ≐
        fraction (RationalTiltedFloorWidth.width (reverseNode i (clock k E T) N a C E)
          (reverseNode (succ i) (clock k E T) N a C E) i two (unit (clock k E T)) M) M := by
    simpa [RationalTiltedFloorWidth.width,correctedNode] using Prf.eqCongr1 (fraction (var 0) (Syn.shift M)) (congrMonus eqNext eqHere)
  exact RationalValueBounds.radius_congr widths.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw

theorem actual_original_unit_floor_width_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⋏ lt (var 0) (var 2)) ⟶
      RationalValueBounds.radius
        (fraction (monus (cut (succ (var 0)) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
          (cut (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) (var 7))
        (RationalArithmetic.add (reverseNode (succ (var 0)) (clock (var 1) (var 5) (var 6)) (var 2) (var 3) (var 4) (var 5))
          (RationalArithmetic.negative (reverseNode (var 0) (clock (var 1) (var 5) (var 6)) (var 2) (var 3) (var 4) (var 5))))
        (two*var 7+two*unit (clock (var 1) (var 5) (var 6))) (var 7*unit (clock (var 1) (var 5) (var 6)))) :=
  closeUniv 8 (.impI (original_width_error _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionFloorWidths
