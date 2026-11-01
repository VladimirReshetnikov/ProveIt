import DiophantineConsistency.AdaptiveAQ30Zeros
import DiophantineConsistency.AdaptiveAQ33Positive
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ30Facts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveAQ30Zeros AdaptiveFirstRootFactor87Syntax
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def bt (p : Fin 4 → ℕ) : Expr (Fin 30) :=
  ((1 + .var 0 * .constant ((p 0:ℕ):ℤ) - .var 1) - .var 2) *
    (.var 6 + .constant ((p 1:ℕ):ℤ) * (1 + .var 0 * .constant ((p 0:ℕ):ℤ))) -
      .var 1 * (1 + .var 0 * .constant ((p 0:ℕ):ℤ))

def wp (p : Fin 4 → ℕ) (v : Fin 30 → V) : V := (splitEval (bt p) v).1 + 1
def wm (p : Fin 4 → ℕ) (v : Fin 30 → V) : V := (splitEval (bt p) v).2 + 1

theorem facts (p : Fin 4 → ℕ) (v : Fin 30 → V)
    (hz : InternalZero (AdaptiveAQ30Literal.literal (fun j => (p j:ℤ))) v) :
    v 20*v 20 = v 13*v 13*(1+v 17*(v 17+(v 9+v 10))) ∧
    v 20+(v 13*(v 9+v 10))*wp p v+wp p v*((1+v 0*(p 0:V))*v 24) =
      v 13*(v 17+(v 9+v 10)+v 8)+v 7*(v 0*(p 0:V))+
        (v 13*(v 9+v 10))*wm p v+wm p v*((1+v 0*(p 0:V))*v 24) := by
  have hall := (sum_zero (fun j => (p j:ℤ)) v).mp hz
  have h0 := hall 0
  have h17 := hall 17
  have h11 := hall 11
  change InternalZero ((.var 20*.var 20) - ((.var 13*.var 13) * (1+.var 26)) : Expr (Fin 30)) v at h0
  change InternalZero (.var 26 - (.var 17*(.var 17+(.var 9+.var 10))) : Expr (Fin 30)) v at h17
  change InternalZero (.var 20 - ((.var 13*((.var 17+(.var 9+.var 10)+.var 8)-((.var 9+.var 10)*(bt p))) + .var 7*(.var 0*.constant ((p 0:ℕ):ℤ))) - ((bt p)*((1+.var 0*.constant ((p 0:ℕ):ℤ))*.var 24))) : Expr (Fin 30)) v at h11
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub,bt] at h0 h17 h11
  refine ⟨?_, ?_⟩
  · rw [← h17]
    exact h0
  · simp [wp,wm,bt,splitEval,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub]
    have h := congrArg (fun x : V => x + (v 13 * (v 9+v 10) + (1+v 0*(p 0:V))*v 24)) h11
    convert h using 1 <;> ring
#print axioms facts
end DiophantineConsistency.AdaptiveAQ30Facts
