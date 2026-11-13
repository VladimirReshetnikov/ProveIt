import Absorb88MainEvaluation

/-! Draft: turn the positive evaluated main root into an oriented balance. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
noncomputable section
namespace Absorb88MainBalance
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPellRecurrence Absorb88MainRoot Absorb88MainEvaluation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_rhs (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    let q : V := 1+v 0*(p 0:V)
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let c : V := v 8+Y*k
    let a : V := X*Y+Y
    let W : V := Y*(q*q)
    (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).2.evalRing (fun j => ι (v j)) =
      (ι W : DiffRing V)*(ι W)*(1+ι (delta a)*ι c*ι c) := by
  simp only [Absorb89Main.mainParts,Absorb89Main.integerPorts,
    Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_var,
    Expr.evalRing_constant,Expr.evalRing_ofNat,Int.cast_natCast,
    map_add,map_mul,map_one,map_ofNat,map_natCast,delta]
  ring

theorem graph_main_balance (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output v) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let c : V := v 8+Y*k
    let a : V := X*Y+Y
    let W : V := Y*(q*q)
    let A : V := (p 1:V)+v 5
    let Bp : V := q*A
    let Bn : V := (v 1+v 2)*A+v 1
    (ι Bp : DiffRing V)<ι Bn →
      ∃ g : V, g*g=1+delta a*c*c ∧
        (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1.evalRing (fun j => ι (v j)) =
          (ι W : DiffRing V)*ι g := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  let c : V := v 8+Y*k
  let a : V := X*Y+Y
  let W : V := Y*(q*q)
  let A : V := (p 1:V)+v 5
  let Bp : V := q*A
  let Bn : V := (v 1+v 2)*A+v 1
  let D : DiffRing V := (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1.evalRing (fun j => ι (v j))
  change (ι Bp : DiffRing V)<ι Bn → ∃ g : V, g*g=1+delta a*c*c ∧ D=ι W*ι g
  intro hn
  obtain ⟨g,hg⟩ := main_root p v hv hz
  change g*g=1+delta a*c*c at hg
  have hD : 0<D := graph_main_root_positive p v hb hv hz hn
  have hzero := main_zero p v hz
  rw [internalZero_iff,Absorb89Main.main_shape] at hzero
  simp only [Expr.evalRing_sub,Expr.evalRing_mul] at hzero
  have hsq := sub_eq_zero.mp hzero
  rw [main_rhs] at hsq
  change D*D=(ι W : DiffRing V)*ι W*(1+ι (delta a)*ι c*ι c) at hsq
  have hgr := congrArg (fun x : V => (ι x : DiffRing V)) hg
  simp only [map_add,map_mul,map_one] at hgr
  have hsquares : D*D=((ι W : DiffRing V)*ι g)*((ι W : DiffRing V)*ι g) := by
    calc
      D*D=(ι W : DiffRing V)*ι W*(1+ι (delta a)*ι c*ι c) := hsq
      _=(ι W : DiffRing V)*ι W*(ι g*ι g) := by rw [hgr]
      _=((ι W : DiffRing V)*ι g)*((ι W : DiffRing V)*ι g) := by ring
  have hwg : (0:DiffRing V)≤ι W*ι g := mul_nonneg (ι_nonneg _) (ι_nonneg _)
  refine ⟨g,hg,?_⟩
  nlinarith

#print axioms Absorb88MainBalance.main_rhs
#print axioms Absorb88MainBalance.graph_main_balance
end Absorb88MainBalance
