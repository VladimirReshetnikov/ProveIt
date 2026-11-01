import DiophantineConsistency.IPRABoundedErasureLogic
import DiophantineConsistency.IPRABoundedSelector
set_option autoImplicit false
namespace DiophantineConsistency.IPRASelectorStability
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

def stableExistsOfSelector (φ : Semipropositionᵢ L 1) (t : Term L ℕ)
    (hselector : Λ ⊢! free φ 🡒 shift (φ/[t]))
    (hstable : Λ ⊢! ∼∼(φ/[t]) 🡒 (φ/[t])) :
    Λ ⊢! ∼∼(∃⁰ φ) 🡒 ∃⁰ φ := by
  have hshift : free ((φ/[t])/[]) = shift (φ/[t]) := by
    have hrew : (Rew.free (L := L) (n := 0)).comp (Rew.subst ![]) = Rew.shift := by
      have hs : (Rew.subst ![] : Rew L ℕ 0 ℕ 1) = Rew.bShift := by
        ext x
        · exact Fin.elim0 x
        · simp
      rw [hs]
      exact Rew.bShift_free_eq_shift
    have he := smul_ext' (φ := φ/[t]) hrew
    rw [TransitiveRewriting.comp_app] at he
    exact he
  have hg : Λ ⊢! free (φ 🡒 ((φ/[t])/[])) := by
    simpa only [LogicalConnective.HomClass.map_imply, hshift] using hselector
  have he : Λ ⊢! (∃⁰ φ) 🡒 (φ/[t]) :=
    HilbertProofᵢ.ex₂ φ (φ/[t]) ⨀ HilbertProofᵢ.gen hg
  have hn : Λ ⊢! ∼∼(∃⁰ φ) 🡒 ∼∼(φ/[t]) := Entailment.contra (Entailment.contra he)
  have hi : Λ ⊢! (φ/[t]) 🡒 ∃⁰ φ := by
    exact (HilbertProofᵢ.ex₁ (Λ := Λ) t φ)
  exact Entailment.C_trans hn (Entailment.C_trans hstable hi)
/-- Transfer stability from a selected decidable characteristic instance.
The forward and reverse pointwise correctness directions are explicit. -/
def stableExistsOfCharacteristic (φ χ : Semipropositionᵢ L 1) (t : Term L ℕ)
    (hforward : Λ ⊢! free φ 🡒 free χ)
    (hselector : Λ ⊢! free χ 🡒 shift (χ/[t]))
    (hstable : Λ ⊢! ∼∼(χ/[t]) 🡒 (χ/[t]))
    (hback : Λ ⊢! (χ/[t]) 🡒 (φ/[t])) :
    Λ ⊢! ∼∼(∃⁰ φ) 🡒 ∃⁰ φ := by
  have hshift : free ((χ/[t])/[]) = shift (χ/[t]) := by
    have hrew : (Rew.free (L := L) (n := 0)).comp (Rew.subst ![]) = Rew.shift := by
      have hs : (Rew.subst ![] : Rew L ℕ 0 ℕ 1) = Rew.bShift := by
        ext x
        · exact Fin.elim0 x
        · simp
      rw [hs]
      exact Rew.bShift_free_eq_shift
    have he := smul_ext' (φ := χ/[t]) hrew
    rw [TransitiveRewriting.comp_app] at he
    exact he
  have hg : Λ ⊢! free (φ 🡒 ((χ/[t])/[])) := by
    simpa only [LogicalConnective.HomClass.map_imply, hshift] using
      (Entailment.C_trans hforward hselector)
  have he : Λ ⊢! (∃⁰ φ) 🡒 (χ/[t]) :=
    HilbertProofᵢ.ex₂ φ (χ/[t]) ⨀ HilbertProofᵢ.gen hg
  have hn : Λ ⊢! ∼∼(∃⁰ φ) 🡒 ∼∼(χ/[t]) := Entailment.contra (Entailment.contra he)
  have hi : Λ ⊢! (φ/[t]) 🡒 ∃⁰ φ := HilbertProofᵢ.ex₁ (Λ := Λ) t φ
  exact Entailment.C_trans hn (Entailment.C_trans hstable (Entailment.C_trans hback hi))
end DiophantineConsistency.IPRASelectorStability
