import FreeMainConditionalRank
import FreeMainAuxNorm

/-! Unchecked draft: actual graph rank, with positive and half-window hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainRankedMain
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open FreeMainConditionalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_at_rank (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀ i, 0<v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)
    (hq : 33≤qval p v)
    (hR : 0<FreeMainAuxNorm.rank p v)
    (hhalf : 2*FreeMainAuxNorm.rank p v<cval p v) :
    ∃ g : V, g*g=1+delta (aval p v)*(cval p v)*(cval p v) ∧
      xcoord (FreeMainAuxNorm.rank p v) (aval p v)=g ∧
      ycoord (FreeMainAuxNorm.rank p v) (aval p v)=cval p v := by
  have hs := FreeMainStrongNorm.strong p v hv hz
  change (v 5*cval p v*cval p v)*(v 5*cval p v*cval p v)+delta (aval p v) =
    delta (aval p v)*(v 4*v 4) at hs
  have ha := FreeMainAuxNorm.auxiliary p v hv hz
  change (let z := absdiff ((v 4*v 4)*(v 6*cval p v))
      ((v 4*v 4)*FreeMainAuxNorm.rank p v+cval p v)
    (v 5*cval p v*cval p v)*(v 5*cval p v*cval p v)*z*z+v 12*v 12 =
      1+(v 5*cval p v*cval p v)*(v 5*cval p v*cval p v)*v 12*v 12) at ha
  exact FreeMainConditionalRank.main_index_eq_rank p v (FreeMainAuxNorm.rank p v)
    hv hz hq hR hhalf hs ha

#print axioms FreeMainRankedMain.main_at_rank
end FreeMainRankedMain
