import PA194ComprehensionLift
import PA194ComprehensionEquality
import PA194InternalOrder
import PA194ConditionalSingleton
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194ComprehensionStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ComprehensionLift PA194ComprehensionEquality PA194InternalOrder PA194ConditionalSingleton
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def Lt {n : Nat} (x y : Bootstrapping.Semiterm V ℒₒᵣ n) : Bootstrapping.Semiformula V ℒₒᵣ n :=
  (⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst ![x,y]
noncomputable def Succ {n : Nat} (x : Bootstrapping.Semiterm V ℒₒᵣ n) : Bootstrapping.Semiterm V ℒₒᵣ n :=
  (⌜(‘#0 + 1’ : ArithmeticSemiterm Nat 1)⌝ : Bootstrapping.Semiterm V ℒₒᵣ 1).subst ![x]

theorem step_body (P : Bootstrapping.Semiformula V ℒₒᵣ 1) (a u v : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar u) 🡘
        (Lt (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) ⋏ P))) 🡒
      (∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar v) 🡘
        (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar u) ⋎
          (((P.subst ![Bootstrapping.Semiterm.fvar a]).subst ![]) ⋏
            ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar a))))) 🡒
      ∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar v) 🡘
        (Lt (Bootstrapping.Semiterm.bvar 0) (Succ (Bootstrapping.Semiterm.fvar a)) ⋏ P)) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let A : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar u)
  let B : Bootstrapping.Semiformula V ℒₒᵣ 1 := Lt (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a)
  let C : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar v)
  let D : Bootstrapping.Semiformula V ℒₒᵣ 1 := Lt (Bootstrapping.Semiterm.bvar 0) (Succ (Bootstrapping.Semiterm.fvar a))
  let E : Bootstrapping.Semiformula V ℒₒᵣ 1 := (Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar a
  let Q : Bootstrapping.Semiformula V ℒₒᵣ 1 := (P.subst ![Bootstrapping.Semiterm.fvar a]).subst ![]
  let U := ∀⁰ (A 🡘 (B ⋏ P))
  let W := ∀⁰ (C 🡘 (A ⋎ (Q ⋏ E)))
  let Z := ∀⁰ (C 🡘 (D ⋏ P))
  change T ⊢ U 🡒 W 🡒 Z
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  have hu : [W,U] ⊢[T]! U := FiniteContext.byAxm (by simp)
  have hw : [W,U] ⊢[T]! W := FiniteContext.byAxm (by simp)
  have ho : [W,U] ⊢[T]! ∀⁰ (D 🡘 (B ⋎ E)) := by
    apply FiniteContext.of
    simpa [D,B,E,Lt,Succ] using (internal_PA_order_explicit a).some
  have he : [W,U] ⊢[T]! ∀⁰ (E 🡒 (P 🡘 Q)) := by
    apply FiniteContext.of
    simpa [E,Q] using (equality_point P a).some
  have hh := (universal_pointwise A B C D E P Q).some
  have h : [W,U] ⊢[T]! U 🡒 W 🡒 (∀⁰ (D 🡘 (B ⋎ E))) 🡒 (∀⁰ (E 🡒 (P 🡘 Q))) 🡒 Z :=
    FiniteContext.of hh
  exact h ⨀ hu ⨀ hw ⨀ ho ⨀ he
#print axioms step_body
end PA194ComprehensionStep
