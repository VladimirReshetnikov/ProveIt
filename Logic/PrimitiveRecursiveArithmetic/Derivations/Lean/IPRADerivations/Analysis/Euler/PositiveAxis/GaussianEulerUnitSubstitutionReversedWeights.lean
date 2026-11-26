import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionReversedDensity
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionTiltedNodes

/-!
# Original signed widths and scalar mesh on the reversed decay grid

The switched order reads the same original density rows once, including
the same power observation and the signed difference of the same two
decay samples. The original Gaussian cell mesh bounds the scalar
distance between these endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionReversedWeights

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionReversedDensity (coarsePowerBody coarseDensityBody leftIndex rightIndex data)
open GaussianEulerUnitSubstitutionTiltedNodes (reverseNode)
open GaussianEulerUnitSubstitutionImageGrid (cellBody node meshNumerator meshDenominator)
open GaussianRationalFiniteSumReversal (reverseBody)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (qsub distanceBounded)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianCoefficientNameBounds (unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def widthBody : PTm 2 := reverseBody cellBody

theorem width_at (i p N z B a C E : PTm n) (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    inst2 widthBody i (data p N z B a C E) ≐ qsub (node (leftIndex N i) p N a C E) (node (rightIndex N i) p N a C E) := by
  let j := leftIndex N i
  have raw := (GaussianRationalFiniteSumReversal.reverse_body_at (Γ := Γ) cellBody i N _).eqTrans
    (GaussianEulerUnitSubstitutionImageGrid.cell_at j p N a C E (GaussianEulerIntegrandName.fixedData z B))
  exact raw.eqTrans (qsub_congr (.eqRefl _) (GaussianEulerDecayMesh.observation_numerator_congr _ _ (E*N) p
    (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (GaussianEulerUnitSubstitutionReversedDensity.reverse_successor N i hi)))))

theorem weighted_body : qmul coarsePowerBody widthBody = coarseDensityBody := by
  simp [coarsePowerBody,widthBody,coarseDensityBody,reverseBody,GaussianEulerUnitSubstitutionDensity.densityBody,cellBody,inst2]

theorem original_weighted_density (p N z B a C E : PTm n) :
    Γ ⊢[PRAAx] sum (qmul coarsePowerBody widthBody) N (data p N z B a C E) ≐
      GaussianEulerUnitSubstitutionDensity.density p N z B a C E := by
  rw [weighted_body]
  exact GaussianEulerUnitSubstitutionReversedDensity.original_density p N z B a C E

theorem original_reversed_mesh (i p N a C E : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionImageGrid.source a C E N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] RationalValueBounds.radius (reverseNode i p N a C E) (reverseNode (succ i) p N a C E)
      (meshNumerator p N C E) (meshDenominator p N E) := by
  let j := leftIndex N i
  let left := node (rightIndex N i) p N a C E
  let right := node j p N a C E
  have hd : Γ ⊢[PRAAx] le one (meshDenominator p N E) :=
    positive_product _ _ (positive_product _ _ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁) (unit_positive p)
  have raw := GaussianEulerUnitSubstitutionImageGrid.original_cell_mesh j p N a C E (one : PTm n) hs
  have code := (GaussianEulerUnitSubstitutionImageGrid.cell_at j p N a C E one).eqTrans
    (qsub_congr (.eqRefl _) (GaussianEulerDecayMesh.observation_numerator_congr _ _ (E*N) p
      (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (GaussianEulerUnitSubstitutionReversedDensity.reverse_successor N i hi)))))
  have near : Γ ⊢[PRAAx] distanceBounded right left (meshNumerator p N C E) (meshDenominator p N E) :=
    GaussianRationalReciprocal.bound_congr code (.eqRefl _) (.eqRefl _) raw
  exact RationalValueBounds.radius_symmetric _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hd near)

theorem actual_original_reversed_scalar_mesh_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((GaussianEulerUnitSubstitutionImageGrid.source (var 3) (var 4) (var 5) (var 2) ⋏ lt (var 0) (var 2)) ⟶
      RationalValueBounds.radius (reverseNode (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (reverseNode (succ (var 0)) (var 1) (var 2) (var 3) (var 4) (var 5))
        (meshNumerator (var 1) (var 2) (var 4) (var 5)) (meshDenominator (var 1) (var 2) (var 5))) :=
  closeUniv 6 (.impI (original_reversed_mesh _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionReversedWeights
