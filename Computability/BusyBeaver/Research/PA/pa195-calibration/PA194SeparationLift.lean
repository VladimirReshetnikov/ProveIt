import PA194SeparationLogic
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194SeparationLift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationLogic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem universal_pointwise (A B C P : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (∀⁰ (A 🡘 (B ⋏ (C ⋏ P)))) 🡒 (∀⁰ (C 🡒 B)) 🡒 ∀⁰ (A 🡘 (C ⋏ P)) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let U1 : Bootstrapping.Semiformula V ℒₒᵣ 1 := A 🡘 (B ⋏ (C ⋏ P))
  let U2 : Bootstrapping.Semiformula V ℒₒᵣ 1 := C 🡒 B
  let W : Bootstrapping.Semiformula V ℒₒᵣ 1 := A 🡘 (C ⋏ P)
  change T ⊢ (∀⁰ U1) 🡒 (∀⁰ U2) 🡒 ∀⁰ W
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply TProof.generalize
  simp only [List.map_cons,List.map_nil]
  let Γ : List (Bootstrapping.Formula V ℒₒᵣ) := [(∀⁰ U2).shift,(∀⁰ U1).shift]
  have h1 : Γ ⊢[T]! ∀⁰ U1.shift := by simpa using (FiniteContext.byAxm (by simp [Γ]) : Γ ⊢[T]! (∀⁰ U1).shift)
  have h2 : Γ ⊢[T]! ∀⁰ U2.shift := by simpa using (FiniteContext.byAxm (by simp [Γ]) : Γ ⊢[T]! (∀⁰ U2).shift)
  have h1' : Γ ⊢[T]! U1.free := TProof.specializeWithCtx h1 (Bootstrapping.Semiterm.fvar 0)
  have h2' : Γ ⊢[T]! U2.free := TProof.specializeWithCtx h2 (Bootstrapping.Semiterm.fvar 0)
  have hp : Γ ⊢[T]! U1.free 🡒 U2.free 🡒 W.free := by
    have ht := (pointwise A.free B.free C.free P.free).some
    apply FiniteContext.of
    simpa [U1,U2,W,Bootstrapping.Semiformula.free] using ht
  exact hp ⨀ h1' ⨀ h2'
#print axioms universal_pointwise
end PA194SeparationLift
