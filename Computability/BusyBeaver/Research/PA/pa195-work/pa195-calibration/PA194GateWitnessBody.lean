import PA194GateWitnessLift
import PA194ComprehensionEquality
import PA194ConditionalSingleton
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PA194GateWitnessBody
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194GateWitnessLift PA194ComprehensionEquality PA194ConditionalSingleton
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gate_body (P D : Bootstrapping.Semiformula V ℒₒᵣ 1) (a b u v : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar u) 🡘
        (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) ⋏ P))) 🡒
      (∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar v) 🡘
        (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar u) ⋎
          (((P.subst ![Bootstrapping.Semiterm.fvar b]).subst ![]) ⋏
            ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar b))))) 🡒
      ∀⁰ (((Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) 🡒 P 🡒
        Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar v)) 🡒
        (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar v) 🡒 P) 🡒 D) 🡒 D) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let A : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar u)
  let B : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a)
  let C : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar v)
  let E : Bootstrapping.Semiformula V ℒₒᵣ 1 := (Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar b
  let Q : Bootstrapping.Semiformula V ℒₒᵣ 1 := (P.subst ![Bootstrapping.Semiterm.fvar b]).subst ![]
  let U := ∀⁰ (A 🡘 (B ⋏ P))
  let W := ∀⁰ (C 🡘 (A ⋎ (Q ⋏ E)))
  let Z := ∀⁰ (((B 🡒 P 🡒 C) 🡒 (C 🡒 P) 🡒 D) 🡒 D)
  change T ⊢ U 🡒 W 🡒 Z
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  have hu : [W,U] ⊢[T]! U := FiniteContext.byAxm (by simp)
  have hw : [W,U] ⊢[T]! W := FiniteContext.byAxm (by simp)
  have he : [W,U] ⊢[T]! ∀⁰ (E 🡒 (P 🡘 Q)) := by
    apply FiniteContext.of
    simpa [E,Q] using (equality_point P b).some
  have h : [W,U] ⊢[T]! U 🡒 W 🡒 (∀⁰ (E 🡒 (P 🡘 Q))) 🡒 Z :=
    FiniteContext.of (universal_rel A B C E P Q D).some
  exact h ⨀ hu ⨀ hw ⨀ he
#print axioms gate_body
end PA194GateWitnessBody
