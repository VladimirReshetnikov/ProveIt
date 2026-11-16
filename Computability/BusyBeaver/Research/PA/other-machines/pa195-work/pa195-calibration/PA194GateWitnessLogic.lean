import PA194ConditionalSingletonLogic
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194GateWitnessLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pointwise (A B C E P Q : Bootstrapping.Formula V ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (A 🡘 (B ⋏ P)) 🡒 (C 🡘 (A ⋎ (Q ⋏ E))) 🡒
      (E 🡒 (P 🡘 Q)) 🡒 ((B 🡒 P 🡒 C) ⋏ (C 🡒 P)) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply FiniteContext.deduct
  let Γ : List (Bootstrapping.Formula V ℒₒᵣ) := [E 🡒 (P 🡘 Q), C 🡘 (A ⋎ (Q ⋏ E)), A 🡘 (B ⋏ P)]
  apply K_intro
  · apply FiniteContext.deduct
    apply FiniteContext.deduct
    let H : List (Bootstrapping.Formula V ℒₒᵣ) := P :: B :: Γ
    have hb : H ⊢[T]! B := FiniteContext.byAxm (by simp [H])
    have hp : H ⊢[T]! P := FiniteContext.byAxm (by simp [H])
    have haEq : H ⊢[T]! A 🡘 (B ⋏ P) := FiniteContext.byAxm (by simp [H,Γ])
    have hcEq : H ⊢[T]! C 🡘 (A ⋎ (Q ⋏ E)) := FiniteContext.byAxm (by simp [H,Γ])
    have ha : H ⊢[T]! A := K_right haEq ⨀ K_intro hb hp
    exact K_right hcEq ⨀ A_intro_left ha
  · apply FiniteContext.deduct
    let H : List (Bootstrapping.Formula V ℒₒᵣ) := C :: Γ
    have hc : H ⊢[T]! C := FiniteContext.byAxm (by simp [H])
    have hcEq : H ⊢[T]! C 🡘 (A ⋎ (Q ⋏ E)) := FiniteContext.byAxm (by simp [H,Γ])
    have hdisj : H ⊢[T]! A ⋎ (Q ⋏ E) := K_left hcEq ⨀ hc
    have hleft : H ⊢[T]! A 🡒 P := by
      apply FiniteContext.deduct
      let J : List (Bootstrapping.Formula V ℒₒᵣ) := A :: H
      have ha : J ⊢[T]! A := FiniteContext.byAxm (by simp [J])
      have haEq : J ⊢[T]! A 🡘 (B ⋏ P) := FiniteContext.byAxm (by simp [J,H,Γ])
      exact K_right (K_left haEq ⨀ ha)
    have hright : H ⊢[T]! (Q ⋏ E) 🡒 P := by
      apply FiniteContext.deduct
      let J : List (Bootstrapping.Formula V ℒₒᵣ) := (Q ⋏ E) :: H
      have hqe : J ⊢[T]! Q ⋏ E := FiniteContext.byAxm (by simp [J])
      have hepq : J ⊢[T]! E 🡒 (P 🡘 Q) := FiniteContext.byAxm (by simp [J,H,Γ])
      have hpq : J ⊢[T]! P 🡘 Q := hepq ⨀ K_right hqe
      exact K_right hpq ⨀ K_left hqe
    exact (CA_of_C_of_C hleft hright) ⨀ hdisj
theorem pointwise_rel (A B C E P Q D : Bootstrapping.Formula V ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (A 🡘 (B ⋏ P)) 🡒 (C 🡘 (A ⋎ (Q ⋏ E))) 🡒
      (E 🡒 (P 🡘 Q)) 🡒 (((B 🡒 P 🡒 C) 🡒 (C 🡒 P) 🡒 D) 🡒 D) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply FiniteContext.deduct
  apply FiniteContext.deduct
  let Γ : List (Bootstrapping.Formula V ℒₒᵣ) :=
    [((B 🡒 P 🡒 C) 🡒 (C 🡒 P) 🡒 D), E 🡒 (P 🡘 Q), C 🡘 (A ⋎ (Q ⋏ E)), A 🡘 (B ⋏ P)]
  have ha : Γ ⊢[T]! A 🡘 (B ⋏ P) := FiniteContext.byAxm (by simp [Γ])
  have hc : Γ ⊢[T]! C 🡘 (A ⋎ (Q ⋏ E)) := FiniteContext.byAxm (by simp [Γ])
  have he : Γ ⊢[T]! E 🡒 (P 🡘 Q) := FiniteContext.byAxm (by simp [Γ])
  have hd : Γ ⊢[T]! (B 🡒 P 🡒 C) 🡒 (C 🡒 P) 🡒 D := FiniteContext.byAxm (by simp [Γ])
  have h := (FiniteContext.of (pointwise A B C E P Q).some : Γ ⊢[T]! _)
  have hb := h ⨀ ha ⨀ hc ⨀ he
  exact hd ⨀ K_left hb ⨀ K_right hb
#print axioms pointwise_rel
#print axioms pointwise
end PA194GateWitnessLogic
