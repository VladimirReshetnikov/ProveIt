import PA194ConditionalSingletonLogic
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace PA194ComprehensionExs
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exs_elim (φ : Bootstrapping.Semiformula V ℒₒᵣ 1) (ψ : Bootstrapping.Formula V ℒₒᵣ)
    (h : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ φ.free 🡒 ψ.shift) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ (∃⁰ φ) 🡒 ψ := by
  classical
  have hc := contra h.some
  have hd : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢! (∼ψ).shift 🡒 (∼φ).free := by
    simpa [Bootstrapping.Semiformula.free] using hc
  have hg : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢! ∼ψ 🡒 ∀⁰ (∼φ) := TProof.generalizeAux hd
  apply Nonempty.intro
  apply C_of_CNN
  simpa using hg
#print axioms exs_elim
end PA194ComprehensionExs
