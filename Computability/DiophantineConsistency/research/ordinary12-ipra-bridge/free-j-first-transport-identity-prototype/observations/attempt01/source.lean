import FreeJAdaptiveLift

/-! Bridge the additive transport identity to the graph's exact first Z. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJFirstTransportIdentity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing Ordinary12FreeJ
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def mExpr (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  let q := 1+(core p).qm
  q*(q*q)*(core p).qm

def ellExpr : Expr (Fin 12) := ((.var 5)*(.var 6))*
  ((.var 6)*((.var 8)+(.var 9)))

def btExpr (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  let q := 1+(core p).qm
  let C := (q-(.var 1))-(.var 2)
  C*((.var 5)+(.constant (p 1))*q)-(.var 1)*q

private theorem z_shape (p : Fin 4 → ℤ) : (core p).z =
    (mExpr p)*((ellExpr+((.var 8)+(.var 9)) + (.var 7))-
      (((.var 8)+(.var 9))*(btExpr p))) +
      (.var 6)*(core p).qm -
      ((1+(core p).qm)*((1+(core p).qm)*(1+(core p).qm)))*(btExpr p) := by rfl

/-- The positive-seed transport identity implies the exact first graph
carrier equation. It does not assert the additive identity or positivity. -/
theorem graph_z_of_additive_transport (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (τ : DiffRing V)
    (h : let ev := fun e : Expr (Fin 12) => e.evalRing (fun j => ι (v j))
      let q := 1+ev (core p).qm
      let k := ι (v 8)+ι (v 9)
      ev (mExpr p)*(ev ellExpr+k+ι (v 7)) + ι (v 6)*ev (core p).qm =
        ev (mExpr p)*τ + (1+ev (core p).qm*k)*(q*(q*q))*ev (btExpr p)) :
    (core p).z.evalRing (fun j => ι (v j)) =
      (mExpr p).evalRing (fun j => ι (v j))*τ := by
  dsimp only at h
  rw [z_shape]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var]
  calc
    _ = ((mExpr p).evalRing (fun j => ι (v j))*
        (ellExpr.evalRing (fun j => ι (v j))+(ι (v 8)+ι (v 9))+ι (v 7)) +
        ι (v 6)*(core p).qm.evalRing (fun j => ι (v j))) -
        ((1+(core p).qm.evalRing (fun j => ι (v j))*(ι (v 8)+ι (v 9)))*
          ((1+(core p).qm.evalRing (fun j => ι (v j)))*
            ((1+(core p).qm.evalRing (fun j => ι (v j)))*
              (1+(core p).qm.evalRing (fun j => ι (v j)))))*
          (btExpr p).evalRing (fun j => ι (v j))) := by ring
    _ = _ := by rw [h]; ring

#print axioms FreeJFirstTransportIdentity.graph_z_of_additive_transport
end FreeJFirstTransportIdentity
