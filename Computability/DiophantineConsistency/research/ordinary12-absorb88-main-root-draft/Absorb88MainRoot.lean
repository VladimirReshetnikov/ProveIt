import Absorb88First
import Absorb89Main
import DiophantineConsistency.ArithmeticPellFirstIndex

/-! Draft: extract the main Pell norm from the actual 88 graph zero. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace Absorb88MainRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticSignedPairs
open ModelDifferenceRing ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveQuotients2011
open ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_same (p : Fin 4 → ℤ) :
    (FreeJAbsorb88.graph p).main=(FreeJAbsorb89.graph p).main := by rfl

theorem main_zero (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output v) :
    InternalZero (FreeJAbsorb89.graph (Absorb89Main.integerPorts p)).main v := by
  rw [internalZero_iff] at hz ⊢
  have hshape : (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output =
      (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).first*
        (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).first+
      (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).main*
        (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).main+
      (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).ordinary*
        (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).ordinary := by rfl
  rw [hshape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_mul] at hz
  have ha := sq_nonneg ((FreeJAbsorb88.graph (Absorb88First.integerPorts p)).first.evalRing (fun j => ι (v j)))
  have hb := sq_nonneg ((FreeJAbsorb88.graph (Absorb88First.integerPorts p)).main.evalRing (fun j => ι (v j)))
  have hc := sq_nonneg ((FreeJAbsorb88.graph (Absorb88First.integerPorts p)).ordinary.evalRing (fun j => ι (v j)))
  have h : (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).main.evalRing (fun j => ι (v j)) *
      (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).main.evalRing (fun j => ι (v j)) = 0 := by nlinarith
  have hm := mul_self_eq_zero.mp h
  change (FreeJAbsorb89.graph (Absorb89Main.integerPorts p)).main.evalRing (fun j => ι (v j)) = 0
  have hp : Absorb88First.integerPorts p = Absorb89Main.integerPorts p := by rfl
  rw [main_same, hp] at hm
  exact hm

theorem main_root (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hv : ∀j, 0<v j)
    (hz : InternalZero (FreeJAbsorb88.graph (Absorb88First.integerPorts p)).output v) :
    let q : V := 1+v 0*(p 0:V)
    let X : V := q*v 5
    let Y : V := (q*(q*q))*v 6
    let k : V := v 8+v 9
    let c : V := v 8+Y*k
    let a : V := X*Y+Y
    ∃ main : V, main*main=1+delta a*c*c := by
  let q : V := 1+v 0*(p 0:V)
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let U : V := Y*(q*q)
  let k : V := v 8+v 9
  let c : V := v 8+Y*k
  let a : V := X*Y+Y
  let H : V := 3+4*a
  change ∃ main : V, main*main=1+delta a*c*c
  have hf := main_zero p v hz
  rw [Absorb89Main.main_shape] at hf
  have hunit : (pairEval (1+((Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1*
      (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1-
      (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).2)) v).1 =
      (pairEval (1+((Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1*
      (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1-
      (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).2)) v).2+1 := by
    have h := congrArg (fun z : V => z+1) hf
    simpa [InternalZero,pairEval,Expr.splitNatural,NatExpr.evalSemiring,add_assoc,add_comm,add_left_comm] using h
  have hs := unit_square_norm (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1
    (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).2 v hunit
  rw [Absorb89Main.rhs_pair p v] at hs
  have hq : 0<q := by dsimp [q]; simp
  have hY : 0<Y := mul_pos (mul_pos hq (mul_pos hq hq)) (hv 6)
  have hU : 0<U := mul_pos hY (mul_pos hq hq)
  have hs' : magnitude (pairEval (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1 v) *
      magnitude (pairEval (Absorb89Main.mainParts (Absorb89Main.integerPorts p)).1 v) =
      U*U*(1+(H+a*a)*(c*c)) := by simpa only [Prod.fst,Prod.snd,add_zero] using hs
  obtain ⟨main,_,hm⟩ := scaled_quotient U _ _ hU hs'
  refine ⟨main,?_⟩
  have hdelta : delta a=H+a*a := by dsimp [delta,H]; ring
  rw [hdelta]
  simpa only [mul_assoc] using hm

#print axioms Absorb88MainRoot.main_same
#print axioms Absorb88MainRoot.main_zero
#print axioms Absorb88MainRoot.main_root
end Absorb88MainRoot
