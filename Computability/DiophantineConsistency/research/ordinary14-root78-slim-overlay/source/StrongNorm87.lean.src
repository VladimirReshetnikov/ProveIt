import FourFields87
import RingNormExtraction

/-! Source-only 87 own-zero strong norm. Slot 7 is the direct Y; the
87 guard is not replaced by an 86 guard. No Lean elaboration is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.StrongNorm87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing FirstFields86Draft AuxRingNormExtractionDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def a (v : Fin 14 → V) : V := v 6*v 7+v 7
def c (v : Fin 14 → V) : V := v 9+v 7*k v
def Delta (v : Fin 14 → V) : V := 3+4*a v+a v*a v

/-- Signed shared strong field for direct Y=slot 7. -/
theorem strong_eval (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    eval (P86ResidueGraph.graph p).gap v=
      (ι (v 4)*ι (c v)*ι (c v))*(ι (v 4)*ι (c v)*ι (c v))-
        ι (Delta v)*(ι (v 3)*ι (v 3)-1) := by
  simp [eval,P86ResidueGraph.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,a,c,Delta,k,
    map_add,map_mul,map_one] <;> ring

/-- Natural strong norm from the 87 graph's own zero. -/
theorem strong_norm (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    (v 4*c v*c v)*(v 4*c v*c v)+Delta v=Delta v*(v 3*v 3) := by
  have hg := (FourFields87Draft.fields_of_zero p v hz).2.2.2
  rw [strong_eval p v] at hg
  exact strong_norm_of_ring_residual _ _ _ _ hg

end DiophantineConsistency.StrongNorm87Draft

#print axioms DiophantineConsistency.StrongNorm87Draft.strong_norm
