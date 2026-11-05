import Absorb88NegativeMainGraph

/-! Draft: connect the expanded oriented root to the graph evaluator. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
noncomputable section
namespace Absorb88MainEvaluation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open Absorb88NegativeMainGraph
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_expression (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let a : V := X*Y+Y
    let W : V := Y*(q*q)
    let H : V := 3+4*a
    let G : DiffRing V := ι (v 2)+(ι b)*(ι q-ι (v 1))
    let rank : DiffRing V := ((ι q)*(ι q)-1)*G+ι (v 0)*(ι (p 2:V)+ι (p 3:V)*ι q)
    (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1.evalRing (fun j => ι (v j)) =
      (ι W : DiffRing V)*(ι X+ι a*(ι (v 8)+ι Y*ι k))+
        ι H*(ι W*ι (v 11)-ι k+rank+1) := by
  simp only [Absorb89Main.mainParts,Absorb89Main.integerPorts,
    Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_var,
    Expr.evalRing_constant,Expr.evalRing_ofNat,Int.cast_natCast,
    map_add,map_mul,map_one,map_ofNat,map_natCast]
  ring

theorem graph_main_root_positive (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    (ι Bp : DiffRing V)<ι Bn →
      0<(Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1.evalRing (fun j => ι (v j)) := by
  dsimp only
  intro hn
  rw [main_expression]
  exact graph_main_positive p v hb hv hz hn

#print axioms Absorb88MainEvaluation.main_expression
#print axioms Absorb88MainEvaluation.graph_main_root_positive
end Absorb88MainEvaluation
