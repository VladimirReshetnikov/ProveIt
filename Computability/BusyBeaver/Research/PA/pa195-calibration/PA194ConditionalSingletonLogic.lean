import PA194InternalSingleton
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.EquationalTheory
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ConditionalSingletonLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma from_singleton (P : Bootstrapping.Semiformula V ℒₒᵣ 1) (B : Bootstrapping.Semiformula V ℒₒᵣ 2) (a z : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (P.subst ![Bootstrapping.Semiterm.fvar a]) 🡒
      (∀⁰ ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z]) 🡘
        ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar a))) 🡒
      (((P.subst ![Bootstrapping.Semiterm.fvar a]) 🡒 B.subst ![Bootstrapping.Semiterm.fvar a,Bootstrapping.Semiterm.fvar z]) ⋏
       (∀⁰ ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z]) 🡒 P))) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let Pa : Bootstrapping.Formula V ℒₒᵣ := P.subst ![Bootstrapping.Semiterm.fvar a]
  let U : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
    (B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z]) 🡘
      ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar a)
  let Vbody : Bootstrapping.Semiformula V ℒₒᵣ 1 := (B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z]) 🡒 P
  let Ba : Bootstrapping.Formula V ℒₒᵣ := B.subst ![Bootstrapping.Semiterm.fvar a,Bootstrapping.Semiterm.fvar z]
  change T ⊢ Pa 🡒 (∀⁰ U) 🡒 ((Pa 🡒 Ba) ⋏ (∀⁰ Vbody))
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply K_intro
  · have hu : [∀⁰ U, Pa] ⊢[T]! ∀⁰ U := FiniteContext.byAxm (by simp)
    have hs : [∀⁰ U, Pa] ⊢[T]! Ba 🡘 ((Bootstrapping.Semiterm.fvar a : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar a) := by
      simpa [U,Ba,Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail] using
        TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar a)
    have he : [∀⁰ U, Pa] ⊢[T]! ((Bootstrapping.Semiterm.fvar a : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar a) :=
      FiniteContext.of (Bootstrapping.Arithmetic.eq_refl (𝗣𝗔 : ArithmeticTheory) (Bootstrapping.Semiterm.fvar a)).some
    exact C_of_conseq (K_right hs ⨀ he)
  · apply TProof.generalize
    simp only [List.map_cons,List.map_nil]
    have hu : [(∀⁰ U).shift, Pa.shift] ⊢[T]! ∀⁰ U.shift := by
      simpa using (FiniteContext.byAxm (by simp) : [(∀⁰ U).shift, Pa.shift] ⊢[T]! (∀⁰ U).shift)
    have hs := TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar 0)
    have hs' : [(∀⁰ U).shift, Pa.shift] ⊢[T]!
        (B.shift.subst ![Bootstrapping.Semiterm.fvar 0,Bootstrapping.Semiterm.fvar (z+1)]) 🡘
          ((Bootstrapping.Semiterm.fvar 0 : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar (a+1)) := by
      simpa [U, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
        Matrix.vecHead, Matrix.vecTail] using hs
    simp only [Vbody, Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_imp,
      Bootstrapping.Semiformula.substs_imp]
    have heq : [(∀⁰ U).shift, Pa.shift] ⊢[T]!
        (B.shift.subst ![Bootstrapping.Semiterm.fvar 0,Bootstrapping.Semiterm.fvar (z+1)]) 🡒
          ((Bootstrapping.Semiterm.fvar 0 : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar (a+1)) := K_left hs'
    have hsym : [(∀⁰ U).shift, Pa.shift] ⊢[T]!
        ((Bootstrapping.Semiterm.fvar 0 : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar (a+1)) 🡒
          ((Bootstrapping.Semiterm.fvar (a+1) : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar 0) :=
      FiniteContext.of (Bootstrapping.Arithmetic.eq_symm (𝗣𝗔 : ArithmeticTheory) (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar (a+1))).some
    have hr : [(∀⁰ U).shift, Pa.shift] ⊢[T]!
        ((Bootstrapping.Semiterm.fvar (a+1) : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar 0) 🡒
          (P.shift.subst ![Bootstrapping.Semiterm.fvar (a+1)]) 🡒 (P.shift.subst ![Bootstrapping.Semiterm.fvar 0]) :=
      FiniteContext.of (Bootstrapping.Arithmetic.replace (𝗣𝗔 : ArithmeticTheory) P.shift (Bootstrapping.Semiterm.fvar (a+1)) (Bootstrapping.Semiterm.fvar 0)).some
    have hp : [(∀⁰ U).shift, Pa.shift] ⊢[T]! P.shift.subst ![Bootstrapping.Semiterm.fvar (a+1)] := by
      simpa [Pa, Bootstrapping.Semiformula.shift_substs] using
        (FiniteContext.byAxm (by simp) : [(∀⁰ U).shift, Pa.shift] ⊢[T]! Pa.shift)
    have ht : [(∀⁰ U).shift, Pa.shift] ⊢[T]!
        ((Bootstrapping.Semiterm.fvar (a+1) : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar 0) 🡒
          (P.shift.subst ![Bootstrapping.Semiterm.fvar 0]) := C_swap hr ⨀ hp
    simpa [Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
      Matrix.vecHead, Matrix.vecTail] using C_trans (C_trans heq hsym) ht
lemma from_empty (P : Bootstrapping.Semiformula V ℒₒᵣ 1) (B : Bootstrapping.Semiformula V ℒₒᵣ 2) (a z : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∼(P.subst ![Bootstrapping.Semiterm.fvar a]) 🡒
      (∀⁰ ∼(B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z])) 🡒
      (((P.subst ![Bootstrapping.Semiterm.fvar a]) 🡒 B.subst ![Bootstrapping.Semiterm.fvar a,Bootstrapping.Semiterm.fvar z]) ⋏
       (∀⁰ ((B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z]) 🡒 P))) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let Pa : Bootstrapping.Formula V ℒₒᵣ := P.subst ![Bootstrapping.Semiterm.fvar a]
  let U : Bootstrapping.Semiformula V ℒₒᵣ 1 := ∼(B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z])
  let Vbody : Bootstrapping.Semiformula V ℒₒᵣ 1 := (B.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar z]) 🡒 P
  let Ba : Bootstrapping.Formula V ℒₒᵣ := B.subst ![Bootstrapping.Semiterm.fvar a,Bootstrapping.Semiterm.fvar z]
  change T ⊢ ∼Pa 🡒 (∀⁰ U) 🡒 ((Pa 🡒 Ba) ⋏ (∀⁰ Vbody))
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply K_intro
  · have hn : [∀⁰ U, ∼Pa] ⊢[T]! ∼Pa := FiniteContext.byAxm (by simp)
    have hprop : [∀⁰ U, ∼Pa] ⊢[T]! ∼Pa 🡒 Pa 🡒 Ba := CNC
    exact hprop ⨀ hn
  · apply TProof.generalize
    simp only [List.map_cons,List.map_nil]
    have hu : [(∀⁰ U).shift, (∼Pa).shift] ⊢[T]! ∀⁰ U.shift := by
      simpa using (FiniteContext.byAxm (by simp) : [(∀⁰ U).shift, (∼Pa).shift] ⊢[T]! (∀⁰ U).shift)
    have hs := TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar 0)
    have hn : [(∀⁰ U).shift, (∼Pa).shift] ⊢[T]!
        ∼(B.shift.subst ![Bootstrapping.Semiterm.fvar 0,Bootstrapping.Semiterm.fvar (z+1)]) := by
      simpa [U, Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
        Matrix.vecHead, Matrix.vecTail] using hs
    have hprop : [(∀⁰ U).shift, (∼Pa).shift] ⊢[T]!
        ∼(B.shift.subst ![Bootstrapping.Semiterm.fvar 0,Bootstrapping.Semiterm.fvar (z+1)]) 🡒
          (B.shift.subst ![Bootstrapping.Semiterm.fvar 0,Bootstrapping.Semiterm.fvar (z+1)]) 🡒
            P.shift.subst ![Bootstrapping.Semiterm.fvar 0] := CNC
    simpa [Vbody, Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_substs,
      Bootstrapping.Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail] using hprop ⨀ hn

#print axioms from_empty
#print axioms from_singleton
end model
end PA194ConditionalSingletonLogic
