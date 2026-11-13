import DiophantineConsistency.Sign33LiftSourceValue
import FreshModel106

/-! Conditional AllCuts-to-source syntax under four explicit port casts. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33AllCutsSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem allcuts_imply_source_zero (p : Fin 4 → ℤ) (ports : Fin 4 → V) (v : Fin 34 → V)
    (hp0 : ((p 0 : ℤ) : DiffRing V) = ι (ports 0))
    (hp1 : ((p 1 : ℤ) : DiffRing V) = ι (ports 1))
    (hp2 : ((p 2 : ℤ) : DiffRing V) = ι (ports 2))
    (hp3 : ((p 3 : ℤ) : DiffRing V) = ι (ports 3))
    (hc : Sign33ResidualAssembly.AllCuts ports v) :
    InternalZero (ObjectCurrentEquation2011.expressionAt p)
      (fun j => v (Fin.castLE (by decide : 15 ≤ 34) (Fin.succ j)) + 1) := by
  have hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j) := by
    intro j
    fin_cases j <;> assumption
  rw [internalZero_iff, FreshModel106.evalRing_expressionAt65]
  simpa only [hp] using Sign33LiftSourceValue.allcuts_imply_value ports v hc
end DiophantineConsistency.Sign33AllCutsSource
#print axioms DiophantineConsistency.Sign33AllCutsSource.allcuts_imply_source_zero
