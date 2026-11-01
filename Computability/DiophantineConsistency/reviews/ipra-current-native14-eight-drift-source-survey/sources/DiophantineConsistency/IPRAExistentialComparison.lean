import DiophantineConsistency.IPRANativeFormulaRew
import Foundation.FirstOrder.NegationTranslation.GoedelGentzen
set_option autoImplicit false
namespace DiophantineConsistency.IPRAExistentialComparison
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRANativeFormulaRew
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

def existsCompare (φ : Semiproposition L 1)
    (h : Λ ⊢! free (φᴺ) 🡒 free (native φ)) :
    Λ ⊢! (∃⁰ φ)ᴺ 🡒 ∼∼(∃⁰ native φ) := by
  have he : Λ ⊢! free (native φ) 🡒 shift (∃⁰ native φ) := by
    change HilbertProofᵢ Λ (free (native φ) 🡒 shift (∃⁰ native φ))
    simpa using (HilbertProofᵢ.ex₁ (Λ := Λ) (&0) (shift (native φ)))
  have hn : Λ ⊢! shift (∼(∃⁰ native φ)) 🡒 free (∼φᴺ) := by
    simpa only [LogicalConnective.HomClass.map_neg] using
      (Entailment.contra (Entailment.C_trans h he))
  have ha : Λ ⊢! ∼(∃⁰ native φ) 🡒 ∀⁰ (∼φᴺ) := HilbertProofᵢ.implyAll hn
  exact Entailment.contra ha
end DiophantineConsistency.IPRAExistentialComparison

namespace DiophantineConsistency.IPRAExistentialComparison
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRANativeFormulaRew
noncomputable def existsCompareUniform {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}
    (φ : Semiproposition L 1) :
    Λ ⊢! (∀⁰ (φᴺ 🡒 native φ)) 🡒 ((∃⁰ φ)ᴺ 🡒 ∼∼(∃⁰ native φ)) := by
  have hpoint : Λ ⊢! free ((φᴺ 🡒 native φ) 🡒 (∼native φ 🡒 ∼φᴺ)) := by
    change Λ ⊢! (free (φᴺ) 🡒 free (native φ)) 🡒
      (∼free (native φ) 🡒 ∼free (φᴺ))
    exact Entailment.CCCNN
  have hmaps : Λ ⊢! (∀⁰ (φᴺ 🡒 native φ)) 🡒 (∀⁰ (∼native φ 🡒 ∼φᴺ)) :=
    HilbertProofᵢ.allImplyAllOfAllImply _ _ ⨀ HilbertProofᵢ.gen hpoint
  have hcontra : Λ ⊢! (∀⁰ (φᴺ 🡒 native φ)) 🡒 ((∀⁰ (∼native φ)) 🡒 (∀⁰ (∼φᴺ))) :=
    Entailment.C_trans hmaps (HilbertProofᵢ.allImplyAllOfAllImply _ _)
  have he : Λ ⊢! free (native φ) 🡒 shift (∃⁰ native φ) := by
    change HilbertProofᵢ Λ (free (native φ) 🡒 shift (∃⁰ native φ))
    simpa using (HilbertProofᵢ.ex₁ (Λ := Λ) (&0) (shift (native φ)))
  have hn : Λ ⊢! shift (∼(∃⁰ native φ)) 🡒 free (∼native φ) := by
    simpa only [LogicalConnective.HomClass.map_neg] using Entailment.contra he
  have hneg : Λ ⊢! ∼(∃⁰ native φ) 🡒 ∀⁰ (∼native φ) := HilbertProofᵢ.implyAll hn
  exact Entailment.C_trans hcontra
    (Entailment.C_trans (Entailment.CCC_of_C_left hneg) Entailment.CCCNN)
end DiophantineConsistency.IPRAExistentialComparison
namespace DiophantineConsistency.IPRAExistentialComparison
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRANativeFormulaRew
noncomputable def theoryExistsCompare {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}
    (φ : Semisentence L 1) (h : T ⊢! ∀⁰ (φᴺ 🡒 native φ)) :
    T ⊢! (∃⁰ φ)ᴺ 🡒 ∼∼(∃⁰ native φ) := by
  have hh := existsCompareUniform (Λ := Λ) (Rewriting.emb φ)
  apply Entailment.mdp ?_ h
  apply Theoryᵢ.ofHilbert
  simpa only [native_rew, Semiformula.emb_doubleNegation,
    LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg, Rewriting.app_all, Rewriting.app_exs, Rew.q_emb] using hh
end DiophantineConsistency.IPRAExistentialComparison
