import PA194ConditionalInsertLogic
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace PA194ConditionalInsertLift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ConditionalInsertLogic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma positive_all (A : Bootstrapping.Formula V ℒₒᵣ)
    (B C E : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ A 🡒 (∀⁰ (C 🡘 (B ⋎ E))) 🡒
      ∀⁰ (C 🡘 (B ⋎ ((A.subst ![]) ⋏ E))) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let U : Bootstrapping.Semiformula V ℒₒᵣ 1 := C 🡘 (B ⋎ E)
  let W : Bootstrapping.Semiformula V ℒₒᵣ 1 := C 🡘 (B ⋎ ((A.subst ![]) ⋏ E))
  change T ⊢ A 🡒 (∀⁰ U) 🡒 ∀⁰ W
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply TProof.generalize
  simp only [List.map_cons,List.map_nil]
  have ha : [(∀⁰ U).shift,A.shift] ⊢[T]! A.shift := FiniteContext.byAxm (by simp)
  have hu : [(∀⁰ U).shift,A.shift] ⊢[T]! ∀⁰ U.shift := by
    simpa using (FiniteContext.byAxm (by simp) : [(∀⁰ U).shift,A.shift] ⊢[T]! (∀⁰ U).shift)
  have hp : [(∀⁰ U).shift,A.shift] ⊢[T]! A.shift 🡒 (C.free 🡘 (B.free ⋎ E.free)) 🡒 (C.free 🡘 (B.free ⋎ (A.shift ⋏ E.free))) :=
    FiniteContext.of (positive A.shift B.free C.free E.free).some
  have hs := TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar 0)
  have hp' : [(∀⁰ U).shift,A.shift] ⊢[T]! A.shift 🡒 U.free 🡒 W.free := by
    simpa [U,W,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
      Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail] using hp
  exact hp' ⨀ ha ⨀ hs
lemma negative_all (A : Bootstrapping.Formula V ℒₒᵣ)
    (B C E : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∼A 🡒 (∀⁰ (C 🡘 B)) 🡒
      ∀⁰ (C 🡘 (B ⋎ ((A.subst ![]) ⋏ E))) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let U : Bootstrapping.Semiformula V ℒₒᵣ 1 := C 🡘 B
  let W : Bootstrapping.Semiformula V ℒₒᵣ 1 := C 🡘 (B ⋎ ((A.subst ![]) ⋏ E))
  change T ⊢ ∼A 🡒 (∀⁰ U) 🡒 ∀⁰ W
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply TProof.generalize
  simp only [List.map_cons,List.map_nil]
  have ha : [(∀⁰ U).shift,(∼A).shift] ⊢[T]! (∼A).shift := FiniteContext.byAxm (by simp)
  have hu : [(∀⁰ U).shift,(∼A).shift] ⊢[T]! ∀⁰ U.shift := by
    simpa using (FiniteContext.byAxm (by simp) : [(∀⁰ U).shift,(∼A).shift] ⊢[T]! (∀⁰ U).shift)
  have hp : [(∀⁰ U).shift,(∼A).shift] ⊢[T]! (∼A).shift 🡒 (C.free 🡘 B.free) 🡒 (C.free 🡘 (B.free ⋎ (A.shift ⋏ E.free))) :=
    by simpa using (FiniteContext.of (negative A.shift B.free C.free E.free).some : [(∀⁰ U).shift,(∼A).shift] ⊢[T]! ∼A.shift 🡒 (C.free 🡘 B.free) 🡒 (C.free 🡘 (B.free ⋎ (A.shift ⋏ E.free))))
  have hs := TProof.specializeWithCtx hu (Bootstrapping.Semiterm.fvar 0)
  have hp' : [(∀⁰ U).shift,(∼A).shift] ⊢[T]! (∼A).shift 🡒 U.free 🡒 W.free := by
    simpa [U,W,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
      Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail] using hp
  exact hp' ⨀ ha ⨀ hs
#print axioms positive_all
#print axioms negative_all
end PA194ConditionalInsertLift
