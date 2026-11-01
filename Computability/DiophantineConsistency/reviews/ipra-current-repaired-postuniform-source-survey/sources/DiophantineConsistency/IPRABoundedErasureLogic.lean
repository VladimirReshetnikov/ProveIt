import Foundation.FirstOrder.Intuitionistic.Deduction

/-! Pure logical steps for erasing a witness bound. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRABoundedErasureLogic
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

/-- Conjunction erasure preserves the two independent child implications. -/
def eraseAnd {a b c d : Propositionᵢ L} (ha : Λ ⊢! a 🡒 c) (hb : Λ ⊢! b 🡒 d) :
    Λ ⊢! a ⋏ b 🡒 c ⋏ d :=
  Entailment.CK_of_C_of_C (Entailment.C_trans Entailment.and₁ ha) (Entailment.C_trans Entailment.and₂ hb)

/-- Disjunction erasure uses disjunction, including for NNF universal guards. -/
def eraseOr {a b c d : Propositionᵢ L} (ha : Λ ⊢! a 🡒 c) (hb : Λ ⊢! b 🡒 d) :
    Λ ⊢! a ⋎ b 🡒 c ⋎ d :=
  Entailment.left_A_intro (Entailment.C_trans ha Entailment.or₁) (Entailment.C_trans hb Entailment.or₂)

/-- Universal erasure, assuming the body implication at a fresh variable. -/
def eraseAll {φ ψ : Semipropositionᵢ L 1} (h : Λ ⊢! free φ 🡒 free ψ) :
    Λ ⊢! ∀⁰ φ 🡒 ∀⁰ ψ := by
  have hg : Λ ⊢! free (φ 🡒 ψ) := by
    change Λ ⊢! free φ 🡒 free ψ
    exact h
  exact Entailment.mdp (allImplyAllOfAllImply φ ψ) (HilbertProofᵢ.gen hg)

/-- An existential guard can be forgotten constructively. -/
def eraseGuardedEx {guard φ ψ : Semipropositionᵢ L 1}
    (h : Λ ⊢! free φ 🡒 free ψ) :
    Λ ⊢! (∃⁰ (guard ⋏ φ)) 🡒 ∃⁰ ψ := by
  have hi : Λ ⊢! free ψ 🡒 shift (∃⁰ ψ) := by
    change HilbertProofᵢ Λ (free ψ 🡒 shift (∃⁰ ψ))
    simpa using (HilbertProofᵢ.ex₁ (Λ := Λ) (&0) (shift ψ))
  have hs : Λ ⊢! free (guard ⋏ φ) 🡒 shift (∃⁰ ψ) :=
    Entailment.C_trans Entailment.and₂ (Entailment.C_trans h hi)
  have hshift : free ((∃⁰ ψ)/[]) = shift (∃⁰ ψ) := by
    have hrew : (Rew.free (L := L) (n := 0)).comp (Rew.subst ![]) = Rew.shift := by
      have hs : (Rew.subst ![] : Rew L ℕ 0 ℕ 1) = Rew.bShift := by
        ext x
        · exact Fin.elim0 x
        · simp
      rw [hs]
      exact Rew.bShift_free_eq_shift
    have he := smul_ext' (φ := ∃⁰ ψ) hrew
    rw [TransitiveRewriting.comp_app] at he
    exact he
  have hg : Λ ⊢! free ((guard ⋏ φ) 🡒 (∃⁰ ψ)/[]) := by
    simpa only [LogicalConnective.HomClass.map_imply, hshift] using hs
  exact HilbertProofᵢ.ex₂ (guard ⋏ φ) (∃⁰ ψ) ⨀ HilbertProofᵢ.gen hg
end DiophantineConsistency.IPRABoundedErasureLogic
