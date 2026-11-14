import PA194ConditionalSingletonLogic
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194ComprehensionLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem pointwise (A B C D E P Q : Bootstrapping.Formula V ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (A 🡘 (B ⋏ P)) 🡒 (C 🡘 (A ⋎ (Q ⋏ E))) 🡒 (D 🡘 (B ⋎ E)) 🡒
      (E 🡒 (P 🡘 Q)) 🡒 (C 🡘 (D ⋏ P)) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply FiniteContext.deduct
  apply FiniteContext.deduct
  let Γ : List (Bootstrapping.Formula V ℒₒᵣ) := [E 🡒 (P 🡘 Q), D 🡘 (B ⋎ E), C 🡘 (A ⋎ (Q ⋏ E)), A 🡘 (B ⋏ P)]
  apply E_intro
  · apply FiniteContext.deduct
    let H : List (Bootstrapping.Formula V ℒₒᵣ) := C :: Γ
    have hc : H ⊢[T]! C := FiniteContext.byAxm (by simp [H])
    have hcEq : H ⊢[T]! C 🡘 (A ⋎ (Q ⋏ E)) := FiniteContext.byAxm (by simp [H,Γ])
    have hdisj : H ⊢[T]! A ⋎ (Q ⋏ E) := K_left hcEq ⨀ hc
    have hleft : H ⊢[T]! A 🡒 (D ⋏ P) := by
      apply FiniteContext.deduct
      let J : List (Bootstrapping.Formula V ℒₒᵣ) := A :: H
      have ha : J ⊢[T]! A := FiniteContext.byAxm (by simp [J])
      have haEq : J ⊢[T]! A 🡘 (B ⋏ P) := FiniteContext.byAxm (by simp [J,H,Γ])
      have hdEq : J ⊢[T]! D 🡘 (B ⋎ E) := FiniteContext.byAxm (by simp [J,H,Γ])
      have hbp : J ⊢[T]! B ⋏ P := K_left haEq ⨀ ha
      have hd : J ⊢[T]! D := K_right hdEq ⨀ A_intro_left (K_left hbp)
      exact K_intro hd (K_right hbp)
    have hright : H ⊢[T]! (Q ⋏ E) 🡒 (D ⋏ P) := by
      apply FiniteContext.deduct
      let J : List (Bootstrapping.Formula V ℒₒᵣ) := (Q ⋏ E) :: H
      have hqe : J ⊢[T]! Q ⋏ E := FiniteContext.byAxm (by simp [J])
      have hdEq : J ⊢[T]! D 🡘 (B ⋎ E) := FiniteContext.byAxm (by simp [J,H,Γ])
      have hepq : J ⊢[T]! E 🡒 (P 🡘 Q) := FiniteContext.byAxm (by simp [J,H,Γ])
      have hd : J ⊢[T]! D := K_right hdEq ⨀ A_intro_right (K_right hqe)
      have hpq : J ⊢[T]! P 🡘 Q := hepq ⨀ K_right hqe
      exact K_intro hd (K_right hpq ⨀ K_left hqe)
    exact (CA_of_C_of_C hleft hright) ⨀ hdisj
  · apply FiniteContext.deduct
    let H : List (Bootstrapping.Formula V ℒₒᵣ) := (D ⋏ P) :: Γ
    have hdp : H ⊢[T]! D ⋏ P := FiniteContext.byAxm (by simp [H])
    have hdEq : H ⊢[T]! D 🡘 (B ⋎ E) := FiniteContext.byAxm (by simp [H,Γ])
    have hdisj : H ⊢[T]! B ⋎ E := K_left hdEq ⨀ K_left hdp
    have hleft : H ⊢[T]! B 🡒 C := by
      apply FiniteContext.deduct
      let J : List (Bootstrapping.Formula V ℒₒᵣ) := B :: H
      have hb : J ⊢[T]! B := FiniteContext.byAxm (by simp [J])
      have hdp' : J ⊢[T]! D ⋏ P := FiniteContext.byAxm (by simp [J,H])
      have haEq : J ⊢[T]! A 🡘 (B ⋏ P) := FiniteContext.byAxm (by simp [J,H,Γ])
      have hcEq : J ⊢[T]! C 🡘 (A ⋎ (Q ⋏ E)) := FiniteContext.byAxm (by simp [J,H,Γ])
      have ha : J ⊢[T]! A := K_right haEq ⨀ K_intro hb (K_right hdp')
      exact K_right hcEq ⨀ A_intro_left ha
    have hright : H ⊢[T]! E 🡒 C := by
      apply FiniteContext.deduct
      let J : List (Bootstrapping.Formula V ℒₒᵣ) := E :: H
      have he : J ⊢[T]! E := FiniteContext.byAxm (by simp [J])
      have hdp' : J ⊢[T]! D ⋏ P := FiniteContext.byAxm (by simp [J,H])
      have hepq : J ⊢[T]! E 🡒 (P 🡘 Q) := FiniteContext.byAxm (by simp [J,H,Γ])
      have hcEq : J ⊢[T]! C 🡘 (A ⋎ (Q ⋏ E)) := FiniteContext.byAxm (by simp [J,H,Γ])
      have hpq : J ⊢[T]! P 🡘 Q := hepq ⨀ he
      have hq : J ⊢[T]! Q := K_left hpq ⨀ K_right hdp'
      exact K_right hcEq ⨀ A_intro_right (K_intro hq he)
    exact (CA_of_C_of_C hleft hright) ⨀ hdisj
#print axioms pointwise
end PA194ComprehensionLogic
