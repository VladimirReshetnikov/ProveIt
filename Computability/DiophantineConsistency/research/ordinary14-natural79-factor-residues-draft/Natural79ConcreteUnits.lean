import Natural79ResidueShapes
import Natural79ZeroWUnits

/-! Source-only composition: all graph cuts, unit lemmas and this client
are unelaborated. No endpoint, iPRA or physical-file theorem is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Natural79ConcreteUnitsDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveFactorMagnitude2011
open Natural79ResidueShapesDraft Natural79ZeroWUnitsDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed literal 79 units at w=0 without assumed residue exclusions. -/
theorem units_of_zero_w_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P79NaturalForcedW.graph p).output v) (hw : v 6=0) :
    (pairEval (P79NaturalForcedW.graph p).first v).1=(pairEval (P79NaturalForcedW.graph p).first v).2+1 ∧
    (pairEval (P79NaturalForcedW.graph p).main v).1=(pairEval (P79NaturalForcedW.graph p).main v).2+1 ∧
    (pairEval (P79NaturalForcedW.graph p).aux v).1=(pairEval (P79NaturalForcedW.graph p).aux v).2+1 ∧
    (pairEval (P79NaturalForcedW.graph p).guardFactor v).1=(pairEval (P79NaturalForcedW.graph p).guardFactor v).2+1 ∧
    (pairEval (P79NaturalForcedW.graph p).strong v).1=(pairEval (P79NaturalForcedW.graph p).strong v).2+1 := by
  obtain ⟨hm,ha,hs⟩ := Natural79ResidueShapesDraft.restricted_residues p v
  exact Natural79ZeroWUnitsDraft.units_of_zero_w_zero p v hz hw hm ha hs

end DiophantineConsistency.Natural79ConcreteUnitsDraft

#print axioms DiophantineConsistency.Natural79ConcreteUnitsDraft.units_of_zero_w_zero
