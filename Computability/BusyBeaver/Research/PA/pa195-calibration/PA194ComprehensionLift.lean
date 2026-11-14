import PA194ComprehensionLogic
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194ComprehensionLift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ComprehensionLogic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem universal_pointwise (A B C D E P Q : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (∀⁰ (A 🡘 (B ⋏ P))) 🡒 (∀⁰ (C 🡘 (A ⋎ (Q ⋏ E)))) 🡒
      (∀⁰ (D 🡘 (B ⋎ E))) 🡒 (∀⁰ (E 🡒 (P 🡘 Q))) 🡒 ∀⁰ (C 🡘 (D ⋏ P)) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let U1 : Bootstrapping.Semiformula V ℒₒᵣ 1 := A 🡘 (B ⋏ P)
  let U2 : Bootstrapping.Semiformula V ℒₒᵣ 1 := C 🡘 (A ⋎ (Q ⋏ E))
  let U3 : Bootstrapping.Semiformula V ℒₒᵣ 1 := D 🡘 (B ⋎ E)
  let U4 : Bootstrapping.Semiformula V ℒₒᵣ 1 := E 🡒 (P 🡘 Q)
  let W : Bootstrapping.Semiformula V ℒₒᵣ 1 := C 🡘 (D ⋏ P)
  change T ⊢ (∀⁰ U1) 🡒 (∀⁰ U2) 🡒 (∀⁰ U3) 🡒 (∀⁰ U4) 🡒 ∀⁰ W
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply FiniteContext.deduct
  apply FiniteContext.deduct
  apply TProof.generalize
  simp only [List.map_cons,List.map_nil]
  let Γ : List (Bootstrapping.Formula V ℒₒᵣ) := [(∀⁰ U4).shift,(∀⁰ U3).shift,(∀⁰ U2).shift,(∀⁰ U1).shift]
  have h1 : Γ ⊢[T]! ∀⁰ U1.shift := by simpa using (FiniteContext.byAxm (by simp [Γ]) : Γ ⊢[T]! (∀⁰ U1).shift)
  have h2 : Γ ⊢[T]! ∀⁰ U2.shift := by simpa using (FiniteContext.byAxm (by simp [Γ]) : Γ ⊢[T]! (∀⁰ U2).shift)
  have h3 : Γ ⊢[T]! ∀⁰ U3.shift := by simpa using (FiniteContext.byAxm (by simp [Γ]) : Γ ⊢[T]! (∀⁰ U3).shift)
  have h4 : Γ ⊢[T]! ∀⁰ U4.shift := by simpa using (FiniteContext.byAxm (by simp [Γ]) : Γ ⊢[T]! (∀⁰ U4).shift)
  have h1' : Γ ⊢[T]! U1.free := TProof.specializeWithCtx h1 (Bootstrapping.Semiterm.fvar 0)
  have h2' : Γ ⊢[T]! U2.free := TProof.specializeWithCtx h2 (Bootstrapping.Semiterm.fvar 0)
  have h3' : Γ ⊢[T]! U3.free := TProof.specializeWithCtx h3 (Bootstrapping.Semiterm.fvar 0)
  have h4' : Γ ⊢[T]! U4.free := TProof.specializeWithCtx h4 (Bootstrapping.Semiterm.fvar 0)
  have hp : Γ ⊢[T]! U1.free 🡒 U2.free 🡒 U3.free 🡒 U4.free 🡒 W.free := by
    have ht := (pointwise A.free B.free C.free D.free E.free P.free Q.free).some
    apply FiniteContext.of
    simpa [U1,U2,U3,U4,W,Bootstrapping.Semiformula.free] using ht
  exact hp ⨀ h1' ⨀ h2' ⨀ h3' ⨀ h4'
#print axioms universal_pointwise
end PA194ComprehensionLift
