import RingParentTo88
import ParentTransportQuotients
import DiophantineConsistency.Compact44.P72Root

/-! Source-only target guard ring binding from an explicit natural transport
balance. No target zero, Lean elaboration or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.ParentTo88GuardDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Target Bt and b at the extended valuation, over any commutative ring. -/
theorem bt_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) (sigma t : R) :
    (P88QuotientGuarded.graph p).Bt.evalRing (RingParentTo88Draft.extend v sigma t)=
      (1+v 0*(p 0 : R)-v 1-v 2)*(v 6+(p 1 : R)*(1+v 0*(p 0 : R)))-
        v 1*(1+v 0*(p 0 : R)) := by
  simp [P88QuotientGuarded.graph,RingParentTo88Draft.extend,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat] <;> ring

theorem b_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 13 → R) (sigma t : R) :
    (P88QuotientGuarded.graph p).b.evalRing (RingParentTo88Draft.extend v sigma t)=v 0*(p 0 : R) := by
  simp [P88QuotientGuarded.graph,RingParentTo88Draft.extend,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant]

/-- Natural transport balance casts to the target quotient guard equality.
No source or target graph zero is assumed in this local statement. -/
theorem guard_of_balance (p : Fin 4 → ℕ) (v : Fin 13 → V) (sigma t : V)
    (hbal : let b := v 0*(p 0:V); let q := 1+b; let A := v 6+(p 1:V)*q
      q*A=(v 1+v 2)*A+v 1*q+b*t) :
    let pi : Fin 4 → ℤ := fun j => (p j : ℤ)
    let w := RingParentTo88Draft.extend (fun j => ι (v j)) (ι sigma) (ι t)
    (P88QuotientGuarded.graph pi).Bt.evalRing w-
      (P88QuotientGuarded.graph pi).b.evalRing w*ι t=0 := by
  let pi : Fin 4 → ℤ := fun j => (p j : ℤ)
  have hp0 : ((pi 0 : ℤ) : DiffRing V)=ι (p 0:V) := P72Root.cast_port p 0
  have hp1 : ((pi 1 : ℤ) : DiffRing V)=ι (p 1:V) := P72Root.cast_port p 1
  have h := congrArg (ι : V →+* DiffRing V) hbal
  simp only [map_add,map_mul,map_one] at h
  rw [bt_eval,b_eval,hp0,hp1]
  dsimp only
  linear_combination h

end DiophantineConsistency.ParentTo88GuardDraft

#print axioms DiophantineConsistency.ParentTo88GuardDraft.guard_of_balance
