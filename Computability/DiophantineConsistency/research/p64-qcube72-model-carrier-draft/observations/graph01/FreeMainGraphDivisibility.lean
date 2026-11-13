import FreeMainCarrierScale
import P64QCube72Free

/-! Unchecked draft: derive q ∣ h from an actual positive 72 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainGraphDivisibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem output_shape (p : Fin 4 → ℤ) : (P64QCube72Free.graph p).output =
    ((P64QCube72Free.graph p).A0*(P64QCube72Free.graph p).Na-1)*
      ((P64QCube72Free.graph p).A0*(P64QCube72Free.graph p).Na-1)+
    (P64QCube72Free.graph p).M*(P64QCube72Free.graph p).M+
    (P64QCube72Free.graph p).W*(P64QCube72Free.graph p).W+
    (P64QCube72Free.graph p).Lt*(P64QCube72Free.graph p).Lt := by rfl

theorem M_eval {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    let q := (p 0:R)*v 0+1
    let Y := q*q*q*v 7
    let U := Y*Y
    let X := v 8*q
    let a := X*Y+Y
    let H := 4*a+3
    let c := (v 10+v 11)*Y+v 10
    let D := U*(X+a*c)+H*v 13
    let N := (a*a+H)*(c*c)+1
    (P64QCube72Free.graph p).M.evalRing v = D*D-U*U*N := by
  simp [P64QCube72Free.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat]

theorem q_dvd_h (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v) :
    ((p 0:V)*v 0+1) ∣ v 13 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let g := P64QCube72Free.graph pp
  let unit := g.A0.evalRing z*g.Na.evalRing z-1
  let m := g.M.evalRing z
  let w := g.W.evalRing z
  let l := g.Lt.evalRing z
  have hs : unit*unit+m*m+w*w+l*l=0 := by
    rw [internalZero_iff,output_shape] at hz
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat,Nat.cast_one] at hz
    exact hz
  have hu := mul_self_nonneg unit
  have hm := mul_self_nonneg m
  have hw := mul_self_nonneg w
  have hl := mul_self_nonneg l
  have hm0 : m=0 := mul_self_eq_zero.mp (by linarith)
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let U : V := Y*Y
  let X : V := v 8*q
  let a : V := X*Y+Y
  let H : V := 4*a+3
  let c : V := (v 10+v 11)*Y+v 10
  let D : V := U*(X+a*c)+H*v 13
  let N : V := (a*a+H)*(c*c)+1
  have hq : 0<q := by dsimp [q]; simp
  have hY : 0<Y := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 7)
  have hU : 0<U := mul_pos hY hY
  have hsq : D*D=U*U*N := by
    change (P64QCube72Free.graph pp).M.evalRing z=0 at hm0
    rw [M_eval] at hm0
    apply ι_injective
    simp only [map_mul,map_add,map_one,map_ofNat]
    dsimp [D,N,U,H,c,a,X,Y,q]
    simp only [pp,z,Int.cast_natCast,map_mul,map_add,map_one,map_ofNat,map_natCast] at hm0
    linear_combination hm0
  exact FreeMainCarrierScale.of_carrier q (v 7) X Y U H (X+a*c) (v 13) D N
    hq hU rfl rfl (by dsimp [H]; ring) rfl hsq

#print axioms FreeMainGraphDivisibility.output_shape
#print axioms FreeMainGraphDivisibility.M_eval
#print axioms FreeMainGraphDivisibility.q_dvd_h
end FreeMainGraphDivisibility
