import FreeJOuterSeedClient

/-! Exact graph identity for the adaptive main-carrier lift. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJAdaptiveLift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing Ordinary12FreeJ
open FreeJOuterSeedClient
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual free-J rank expression. -/
def rankExpr (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  let J : Expr (Fin 12) := .var 0
  let F : Expr (Fin 12) := .var 1
  let alpha : Expr (Fin 12) := .var 2
  let qm := J * (.constant (p 0))
  let q := 1+qm
  let G := alpha+(q-F)*qm
  G*(q*q-1)+J*((.constant (p 2))+(.constant (p 3))*q)

def shiftExpr (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  ((.var 8)+(.var 9))-rankExpr p-1

private theorem block_u_shape (p : Fin 4 → ℤ) : (core p).u =
    (.var 6)*((1+(core p).qm)*(1+(core p).qm)) := by rfl

private theorem block_d_shape (p : Fin 4 → ℤ) : (core p).d =
    (core p).u*((.var 5)+(core p).a*(core p).c) +
      (3+4*(core p).a)*((core p).u*(.var 11)+
        ((.var 5)*(.var 6))*(1+(core p).qm)-shiftExpr p) := by rfl

/-- If X=q*w and the chosen graph gamma satisfies the displayed linear lift,
then the actual Dstar equals U times the unlifted main-Pell ordinate. The
existence, integrality and positivity of the chosen gamma are not asserted. -/
theorem main_lift_identity (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (w gammaOld : DiffRing V)
    (hX : ι (v 5) = (1+(core p).qm.evalRing (fun j => ι (v j)))*w)
    (hlift : (core p).u.evalRing (fun j => ι (v j))*ι (v 11) +
      (core p).u.evalRing (fun j => ι (v j))*w =
      (core p).u.evalRing (fun j => ι (v j))*gammaOld +
        (shiftExpr p).evalRing (fun j => ι (v j))) :
    (core p).d.evalRing (fun j => ι (v j)) =
      (core p).u.evalRing (fun j => ι (v j))*
        (ι (v 5)+(core p).a.evalRing (fun j => ι (v j))*
          (core p).c.evalRing (fun j => ι (v j))+
          gammaOld*(4*(core p).a.evalRing (fun j => ι (v j))+3)) := by
  have hqE : ((ι (v 5))*(ι (v 6)))*
      (1+(core p).qm.evalRing (fun j => ι (v j))) =
      (core p).u.evalRing (fun j => ι (v j))*w := by
    rw [block_u_shape]
    simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_ofNat]
    rw [hX]
    ring
  have hlift' : (core p).u.evalRing (fun j => ι (v j))*ι (v 11)+
      (core p).u.evalRing (fun j => ι (v j))*w-
        (shiftExpr p).evalRing (fun j => ι (v j)) =
      (core p).u.evalRing (fun j => ι (v j))*gammaOld := by
    rw [hlift]
    ring
  rw [block_d_shape]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_var, Expr.evalRing_ofNat]
  rw [hqE,hlift']
  ring

#print axioms FreeJAdaptiveLift.main_lift_identity
end FreeJAdaptiveLift
