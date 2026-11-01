import DiophantineConsistency.AdaptiveDirectOrdinate86Reverse
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace DiophantineConsistency.AdaptiveVReverseSign
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context
open AdaptiveDirectOrdinate86AuxNorm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eV_congr (p : Fin 4 → ℤ) (u w : Fin 13 → V)
    (h : ∀ i, i ≠ 11 → w i = u i) : pairEval (eV p) w = pairEval (eV p) u := by
  change splitEval (eV p) w = splitEval (eV p) u
  simp only [eV,eC]
  simp only [splitEval, Expr.splitNatural, NatExpr.evalSemiring]
  rw [h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide),h 5 (by decide),h 7 (by decide),h 9 (by decide),h 10 (by decide)]
#print axioms eV_congr
end DiophantineConsistency.AdaptiveVReverseSign
