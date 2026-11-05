import FreeMainGraphDivisibility
import DiophantineConsistency.ArithmeticAdaptiveQuotients2011
import DiophantineConsistency.ArithmeticPellClassification

/-! Unchecked draft: actual 72-zero main Pell root and index. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainGraphMainRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticAdaptiveQuotients2011 ArithmeticPellClassification ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_root (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v) :
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let U := Y*Y
    let X := v 8*q
    let a := X*Y+Y
    let H := 4*a+3
    let c := (v 10+v 11)*Y+v 10
    ∃ g : V, g*g = (a*a+H)*(c*c)+1 ∧
      U*g = U*(X+a*c)+H*v 13 := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let gr := P64QCube72Free.graph pp
  let unit := gr.A0.evalRing z*gr.Na.evalRing z-1
  let m := gr.M.evalRing z
  let w := gr.W.evalRing z
  let l := gr.Lt.evalRing z
  have hs : unit*unit+m*m+w*w+l*l=0 := by
    rw [internalZero_iff,FreeMainGraphShape.output_shape] at hz
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
    rw [FreeMainGraphShape.M_eval] at hm0
    have hh : (ι D : DiffRing V)*(ι D) - (ι U)*(ι U)*(ι N) = 0 := by
      simpa [pp,z,D,N,U,H,c,a,X,Y,q, map_mul,map_add,map_one,map_ofNat,map_natCast] using hm0
    apply ι_injective
    simpa only [map_mul] using sub_eq_zero.mp hh
  obtain ⟨g,hD,hn⟩ := scaled_quotient U D N hU hsq
  exact ⟨g,hn,hD.symm⟩

theorem main_index (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v) :
    let q : V := (p 0:V)*v 0+1
    let Y := q*q*q*v 7
    let U := Y*Y
    let X := v 8*q
    let a := X*Y+Y
    let H := 4*a+3
    let c := (v 10+v 11)*Y+v 10
    ∃ g m : V, g*g=1+delta a*c*c ∧
      U*g=U*(X+a*c)+H*v 13 ∧
      xcoord m a=g ∧ ycoord m a=c := by
  let q : V := (p 0:V)*v 0+1
  let Y : V := q*q*q*v 7
  let U : V := Y*Y
  let X : V := v 8*q
  let a : V := X*Y+Y
  let H : V := 4*a+3
  let c : V := (v 10+v 11)*Y+v 10
  obtain ⟨g,hg,hcarrier⟩ := main_root p v hv hz
  change g*g=(a*a+H)*(c*c)+1 at hg
  change U*g=U*(X+a*c)+H*v 13 at hcarrier
  have hnorm : g*g=1+delta a*c*c := by
    rw [hg]
    unfold delta
    dsimp [H]
    ring
  obtain ⟨m,_,hx,hy⟩ := solution_index a g c hnorm
  exact ⟨g,m,hnorm,hcarrier,hx,hy⟩

#print axioms FreeMainGraphMainRoot.main_root
#print axioms FreeMainGraphMainRoot.main_index
end FreeMainGraphMainRoot
