import PA194InternalBitInsert
import PA194ConditionalSingletonLogic
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194ConditionalInsertLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma positive (A B C E : Bootstrapping.Formula V ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ A 🡒 (C 🡘 (B ⋎ E)) 🡒 (C 🡘 (B ⋎ (A ⋏ E))) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  let G : List (Bootstrapping.Formula V ℒₒᵣ) := [C 🡘 (B ⋎ E), A]
  have ha : G ⊢[T]! A := FiniteContext.byAxm (by simp [G])
  have he : G ⊢[T]! C 🡘 (B ⋎ E) := FiniteContext.byAxm (by simp [G])
  apply K_intro
  · apply FiniteContext.deduct
    let H : List (Bootstrapping.Formula V ℒₒᵣ) := C :: G
    have hc : H ⊢[T]! C := FiniteContext.byAxm (by simp [H])
    have ha' : H ⊢[T]! A := FiniteContext.byAxm (by simp [H,G])
    have he' : H ⊢[T]! C 🡘 (B ⋎ E) := FiniteContext.byAxm (by simp [H,G])
    have hd : H ⊢[T]! B ⋎ E := K_left he' ⨀ hc
    have h1 : H ⊢[T]! B 🡒 B ⋎ (A ⋏ E) := or₁
    have h2 : H ⊢[T]! E 🡒 B ⋎ (A ⋏ E) := by
      apply FiniteContext.deduct
      have ha'' : (E :: H) ⊢[T]! A := FiniteContext.byAxm (by simp [H,G])
      have he'' : (E :: H) ⊢[T]! E := FiniteContext.byAxm (by simp)
      exact A_intro_right (K_intro ha'' he'')
    have h3 : H ⊢[T]! (B ⋎ E) 🡒 (B ⋎ (A ⋏ E)) := CA_of_C_of_C h1 h2
    exact h3 ⨀ hd
  · apply FiniteContext.deduct
    let H : List (Bootstrapping.Formula V ℒₒᵣ) := (B ⋎ (A ⋏ E)) :: G
    have he' : H ⊢[T]! C 🡘 (B ⋎ E) := FiniteContext.byAxm (by simp [H,G])
    have hd : H ⊢[T]! B ⋎ (A ⋏ E) := FiniteContext.byAxm (by simp [H])
    have h1 : H ⊢[T]! B 🡒 B ⋎ E := or₁
    have h2 : H ⊢[T]! (A ⋏ E) 🡒 B ⋎ E := by
      apply FiniteContext.deduct
      have h : ((A ⋏ E) :: H) ⊢[T]! A ⋏ E := FiniteContext.byAxm (by simp)
      exact A_intro_right (K_right h)
    have h3 : H ⊢[T]! (B ⋎ (A ⋏ E)) 🡒 (B ⋎ E) := CA_of_C_of_C h1 h2
    have h4 : H ⊢[T]! B ⋎ E := h3 ⨀ hd
    exact K_right he' ⨀ h4
lemma negative (A B C E : Bootstrapping.Formula V ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∼A 🡒 (C 🡘 B) 🡒 (C 🡘 (B ⋎ (A ⋏ E))) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  let G : List (Bootstrapping.Formula V ℒₒᵣ) := [C 🡘 B, ∼A]
  apply K_intro
  · apply FiniteContext.deduct
    let H : List (Bootstrapping.Formula V ℒₒᵣ) := C :: G
    have hc : H ⊢[T]! C := FiniteContext.byAxm (by simp [H])
    have he : H ⊢[T]! C 🡘 B := FiniteContext.byAxm (by simp [H,G])
    exact A_intro_left (K_left he ⨀ hc)
  · apply FiniteContext.deduct
    let H : List (Bootstrapping.Formula V ℒₒᵣ) := (B ⋎ (A ⋏ E)) :: G
    have hn : H ⊢[T]! ∼A := FiniteContext.byAxm (by simp [H,G])
    have he : H ⊢[T]! C 🡘 B := FiniteContext.byAxm (by simp [H,G])
    have hd : H ⊢[T]! B ⋎ (A ⋏ E) := FiniteContext.byAxm (by simp [H])
    have h1 : H ⊢[T]! B 🡒 B := C_id
    have h2 : H ⊢[T]! (A ⋏ E) 🡒 B := by
      apply FiniteContext.deduct
      have hn' : ((A ⋏ E) :: H) ⊢[T]! ∼A := FiniteContext.byAxm (by simp [H,G])
      have he' : ((A ⋏ E) :: H) ⊢[T]! A ⋏ E := FiniteContext.byAxm (by simp)
      have hc : ((A ⋏ E) :: H) ⊢[T]! ∼A 🡒 A 🡒 B := CNC
      exact hc ⨀ hn' ⨀ K_left he'
    have h3 : H ⊢[T]! (B ⋎ (A ⋏ E)) 🡒 B := CA_of_C_of_C h1 h2
    exact K_right he ⨀ (h3 ⨀ hd)
#print axioms positive
#print axioms negative
end PA194ConditionalInsertLogic
