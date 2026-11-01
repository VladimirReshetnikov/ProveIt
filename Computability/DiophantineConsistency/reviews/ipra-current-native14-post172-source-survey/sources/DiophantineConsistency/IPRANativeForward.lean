import DiophantineConsistency.IPRANativeFormulaRew

/-! Native NNF implies its Gödel–Gentzen image in intuitionistic logic. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace DiophantineConsistency.IPRANativeForward
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ IPRANativeFormula IPRANativeFormulaRew
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

private def allMono {φ ψ : Semipropositionᵢ L 1}
    (h : Λ ⊢! free φ 🡒 free ψ) : Λ ⊢! ∀⁰ φ 🡒 ∀⁰ ψ := by
  have hg : Λ ⊢! free (φ 🡒 ψ) := by
    change Λ ⊢! free φ 🡒 free ψ
    exact h
  exact Entailment.mdp (allImplyAllOfAllImply φ ψ) (HilbertProofᵢ.gen hg)

/-- Every native NNF reading implies the GG translation, by logic alone. -/
def nativeForward : (φ : Proposition L) → Λ ⊢! native φ 🡒 φᴺ
  | .rel r v => Entailment.dni
  | .nrel r v => Entailment.C_id
  | ⊤ => Entailment.C_id
  | ⊥ => Entailment.C_id
  | φ ⋏ ψ =>
    Entailment.CK_of_C_of_C
      (Entailment.C_trans Entailment.and₁ (nativeForward φ))
      (Entailment.C_trans Entailment.and₂ (nativeForward ψ))
  | φ ⋎ ψ =>
    Entailment.left_A_intro
      (Entailment.C_trans (nativeForward φ) (Entailment.C_trans Entailment.dni (Entailment.contra Entailment.and₁)))
      (Entailment.C_trans (nativeForward ψ) (Entailment.C_trans Entailment.dni (Entailment.contra Entailment.and₂)))
  | ∀⁰ φ => by
    have ih := nativeForward (free φ)
    apply allMono
    simpa only [native_rew, Semiformula.rew_doubleNegation] using ih
  | ∃⁰ φ => by
    have ih := nativeForward (free φ)
    have hc : Λ ⊢! ∼free (φᴺ) 🡒 ∼free (native φ) := by
      apply Entailment.contra
      simpa only [native_rew, Semiformula.rew_doubleNegation] using ih
    have hall : Λ ⊢! ∀⁰ (∼φᴺ) 🡒 ∀⁰ (∼native φ) := allMono hc
    have hex : Λ ⊢! ∀⁰ (∼native φ) 🡒 ∼(∃⁰ (native φ)) := by
      change HilbertProofᵢ Λ (∀⁰ (∼native φ) 🡒 ∼(∃⁰ (native φ)))
      simpa [Semiformulaᵢ.neg_def] using
        (HilbertProofᵢ.ex₂ (Λ := Λ) (native φ) (⊥ : Propositionᵢ L))
    exact Entailment.C_trans Entailment.dni (Entailment.contra (Entailment.C_trans hall hex))
  termination_by φ => φ.complexity
end DiophantineConsistency.IPRANativeForward
