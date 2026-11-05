import DiophantineConsistency.SharingNormSquares
import DiophantineConsistency.NormAssignment38

/-! UNCOMPILED DRAFT. Exact slot-to-gate identities and conditional extraction.
Imports, tactic scripts and every theorem in this file are unverified. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def residuals (p : Fin 4 → ℤ) : List (Expr (Fin 39)) :=
  SharingSeed38.firstResidual p :: SharingSeed38.remainingResiduals p

def residualAt (p : Fin 4 → ℤ) (i : Fin 29) : Expr (Fin 39) :=
  (residuals p).get ⟨i.val, by simpa [residuals, SharingSeed38.remainingResiduals] using i.isLt⟩


end DiophantineConsistency.Norm38SlotExtraction
