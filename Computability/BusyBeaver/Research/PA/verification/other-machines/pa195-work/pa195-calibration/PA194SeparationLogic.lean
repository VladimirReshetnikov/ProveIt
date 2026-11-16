import PA194ConditionalSingletonLogic
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace PA194SeparationLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem pointwise (A B C P : Bootstrapping.Formula V ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ (A 🡘 (B ⋏ (C ⋏ P))) 🡒 (C 🡒 B) 🡒 (A 🡘 (C ⋏ P)) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  apply Nonempty.intro
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  let Γ : List (Bootstrapping.Formula V ℒₒᵣ) := [C 🡒 B,A 🡘 (B ⋏ (C ⋏ P))]
  have he : Γ ⊢[T]! A 🡘 (B ⋏ (C ⋏ P)) := FiniteContext.byAxm (by simp [Γ])
  apply E_intro
  · apply FiniteContext.deduct
    have ha : (A :: Γ) ⊢[T]! A := FiniteContext.byAxm (by simp)
    have he' : (A :: Γ) ⊢[T]! A 🡘 (B ⋏ (C ⋏ P)) := FiniteContext.weakening (by simp) he
    exact K_right (K_left he' ⨀ ha)
  · apply FiniteContext.deduct
    have hcp : ((C ⋏ P) :: Γ) ⊢[T]! C ⋏ P := FiniteContext.byAxm (by simp)
    have hcb : ((C ⋏ P) :: Γ) ⊢[T]! C 🡒 B := FiniteContext.byAxm (by simp [Γ])
    have he' : ((C ⋏ P) :: Γ) ⊢[T]! A 🡘 (B ⋏ (C ⋏ P)) := FiniteContext.weakening (by simp) he
    exact K_right he' ⨀ K_intro (hcb ⨀ K_left hcp) hcp
#print axioms pointwise
end PA194SeparationLogic
