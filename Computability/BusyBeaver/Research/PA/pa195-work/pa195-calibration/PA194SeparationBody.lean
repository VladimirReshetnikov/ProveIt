import PA194SeparationLift
import PA194InternalBitBound
import PA194ComprehensionStep
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194SeparationBody
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationLift PA194InternalBitBound PA194ConditionalSingleton PA194ComprehensionStep
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem separation_body (P : Bootstrapping.Semiformula V ℒₒᵣ 1) (a s : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar s) 🡘
        (Lt (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) ⋏
          (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) ⋏ P)))) 🡒
      ∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar s) 🡘
        (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) ⋏ P)) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let A : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar s)
  let B : Bootstrapping.Semiformula V ℒₒᵣ 1 := Lt (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a)
  let C : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a)
  let U := ∀⁰ (A 🡘 (B ⋏ (C ⋏ P)))
  let W := ∀⁰ (A 🡘 (C ⋏ P))
  change T ⊢ U 🡒 W
  apply Nonempty.intro
  apply FiniteContext.deduct'
  have hu : [U] ⊢[T]! U := FiniteContext.byAxm (by simp)
  have hb : [U] ⊢[T]! ∀⁰ (C 🡒 B) := by
    apply FiniteContext.of
    simpa [C,B,PA194ConditionalSingleton.Bit,Lt] using (internal_PA_bound_explicit a).some
  have h : [U] ⊢[T]! U 🡒 (∀⁰ (C 🡒 B)) 🡒 W :=
    FiniteContext.of (universal_pointwise A B C P).some
  exact h ⨀ hu ⨀ hb
#print axioms separation_body
end PA194SeparationBody
