import DiophantineConsistency.IPRASuccLeft
import Foundation.Meta.IntProver
set_option autoImplicit false
namespace DiophantineConsistency.IPRAReconstructLogic
open LO LO.FirstOrder LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRALanguage PRATheory
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem reconstruction_step_logic (P Z R J Q : Propositionᵢ language) : (𝗜𝗻𝘁¹ : Hilbertᵢ language) ⊢
    (P ⋎ ∼P) 🡒 (Z ⋎ R) 🡒 (Z 🡒 P) 🡒 (Z ⋎ J) 🡒 (J 🡒 R 🡒 Q) 🡒 (P ⋎ Q) := by
  have hh : [] ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ language)]
      (P ⋎ ∼P) 🡒 (Z ⋎ R) 🡒 (Z 🡒 P) 🡒 (Z ⋎ J) 🡒 (J 🡒 R 🡒 Q) 🡒 (P ⋎ Q) := by
    apply FiniteContext.deduct!
    apply FiniteContext.deduct!
    apply FiniteContext.deduct!
    apply FiniteContext.deduct!
    apply FiniteContext.deduct!
    let G : List (Propositionᵢ language) := [J 🡒 R 🡒 Q, Z ⋎ J, Z 🡒 P, Z ⋎ R, P ⋎ ∼P]
    have hd : G ⊢[𝗜𝗻𝘁¹] P ⋎ ∼P := ⟨FiniteContext.byAxm (by simp [G])⟩
    have hl : G ⊢[𝗜𝗻𝘁¹] P 🡒 P ⋎ Q := ⟨Entailment.or₁⟩
    have hr : G ⊢[𝗜𝗻𝘁¹] ∼P 🡒 P ⋎ Q := by
      apply FiniteContext.deduct!
      let H : List (Propositionᵢ language) := ∼P :: G
      have hn : H ⊢[𝗜𝗻𝘁¹] ∼P := ⟨FiniteContext.byAxm (by simp [H])⟩
      have hzp : H ⊢[𝗜𝗻𝘁¹] Z 🡒 P := ⟨FiniteContext.byAxm (by simp [H,G])⟩
      have hnz : H ⊢[𝗜𝗻𝘁¹] ∼Z := ⟨Entailment.contra (Classical.choice hzp) ⨀ Classical.choice hn⟩
      have hzr : H ⊢[𝗜𝗻𝘁¹] Z ⋎ R := ⟨FiniteContext.byAxm (by simp [H,G])⟩
      have hzj : H ⊢[𝗜𝗻𝘁¹] Z ⋎ J := ⟨FiniteContext.byAxm (by simp [H,G])⟩
      have hR : H ⊢[𝗜𝗻𝘁¹] R := Entailment.A!_cases (Entailment.C_of_N hnz) (⟨Entailment.C_id⟩) hzr
      have hJ : H ⊢[𝗜𝗻𝘁¹] J := Entailment.A!_cases (Entailment.C_of_N hnz) (⟨Entailment.C_id⟩) hzj
      have hjrq : H ⊢[𝗜𝗻𝘁¹] J 🡒 R 🡒 Q := ⟨FiniteContext.byAxm (by simp [H,G])⟩
      have hq := Entailment.mdp! (Entailment.mdp! hjrq hJ) hR
      exact Entailment.A!_intro_right hq
    exact Entailment.A!_cases hl hr hd
  exact ⟨FiniteContext.emptyPrf (Classical.choice hh)⟩
end DiophantineConsistency.IPRAReconstructLogic
