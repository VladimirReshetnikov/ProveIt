import PA194ConditionalInsert
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PA194GateInsertPoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ConditionalSingleton
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem insertion_point (A : Bootstrapping.Formula V ℒₒᵣ) (b u v : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar v) 🡘
        (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar u) ⋎
          ((A.subst ![]) ⋏ ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar b))))) 🡒
      A 🡒 Bit (Bootstrapping.Semiterm.fvar b) (Bootstrapping.Semiterm.fvar v) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let B : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar u)
  let C : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar v)
  let E : Bootstrapping.Semiformula V ℒₒᵣ 1 := (Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar b
  let U := ∀⁰ (C 🡘 (B ⋎ ((A.subst ![]) ⋏ E)))
  change T ⊢ U 🡒 A 🡒 Bit (Bootstrapping.Semiterm.fvar b) (Bootstrapping.Semiterm.fvar v)
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  have hu : [A,U] ⊢[T]! U := FiniteContext.byAxm (by simp)
  have ha : [A,U] ⊢[T]! A := FiniteContext.byAxm (by simp)
  have hspec : [A,U] ⊢[T]! (C.subst ![Bootstrapping.Semiterm.fvar b]) 🡘
      (B.subst ![Bootstrapping.Semiterm.fvar b] ⋎
        ((A.subst ![]).subst ![Bootstrapping.Semiterm.fvar b] ⋏ E.subst ![Bootstrapping.Semiterm.fvar b])) := by
    simpa [U] using TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar b)
  have heq : [A,U] ⊢[T]! ((Bootstrapping.Semiterm.fvar b : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar b) :=
    FiniteContext.of (Bootstrapping.Arithmetic.eq_refl (𝗣𝗔 : ArithmeticTheory) (Bootstrapping.Semiterm.fvar b)).some
  have hb : [A,U] ⊢[T]! C.subst ![Bootstrapping.Semiterm.fvar b] := by
    have hr : [A,U] ⊢[T]! (A.subst ![]).subst ![Bootstrapping.Semiterm.fvar b] ⋏ E.subst ![Bootstrapping.Semiterm.fvar b] := by
      simpa [E,Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using K_intro ha heq
    have hd : [A,U] ⊢[T]! B.subst ![Bootstrapping.Semiterm.fvar b] ⋎ ((A.subst ![]).subst ![Bootstrapping.Semiterm.fvar b] ⋏ E.subst ![Bootstrapping.Semiterm.fvar b]) := A_intro_right hr
    simpa using K_right hspec ⨀ hd
  simpa [C,PA194ConditionalSingleton.Bit,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using hb
#print axioms insertion_point
end PA194GateInsertPoint
