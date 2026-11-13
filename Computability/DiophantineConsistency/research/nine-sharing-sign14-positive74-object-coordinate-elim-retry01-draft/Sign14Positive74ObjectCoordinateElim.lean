import DiophantineConsistency.Sign14Positive74ObjectGuardBind

/-! SOURCE-ONLY: extract individual nonzero and reconstruction implications. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectCoordinateElim
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRAFiniteFunctionCodes IPRANativeTheory
open IPRATheoryHilbertBridge IPRANativeAtomStability Sign14Positive74ObjectPredecessor
open Sign14Positive74ObjectGuardReconstruct
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem listConjElim : (xs : List (Propositionᵢ language)) → (p : Propositionᵢ language) →
    p ∈ xs → extended nativeTheory ⊢ ((⋀ xs) 🡒 p)
  | [], _, h => by simp at h
  | [x], p, h => by
    simp only [List.mem_singleton] at h
    subst p
    exact ⟨by simpa using (Entailment.C_id (φ := x))⟩
  | x :: y :: xs, p, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨by simpa only [List.conj₂] using (Entailment.and₁ : extended nativeTheory ⊢! (x ⋏ ⋀ (y :: xs)) 🡒 x)⟩
    · have ih := listConjElim (y :: xs) p h
      exact ⟨by simpa only [List.conj₂] using (Entailment.C_trans Entailment.and₂ (Classical.choice ih))⟩

def nonzeroAt (v : Fin 14 → Term language ℕ) (i : Fin 14) :
    extended nativeTheory ⊢! (nonzeroGuardOpen v 🡒 ∼eqAt (v i) zero) := by
  apply Classical.choice
  apply listConjElim
  exact List.mem_map.mpr ⟨i, by simp, rfl⟩

def reconstructionAt (v : Fin 14 → Term language ℕ) (i : Fin 14) :
    extended nativeTheory ⊢! (nonzeroGuardOpen v 🡒 eqAt (v i) (succ (pred (v i)))) :=
  Entailment.C_trans (nonzeroAt v i) (nonzeroReconstructionOpen (v i))
end DiophantineConsistency.Sign14Positive74ObjectCoordinateElim
#print axioms DiophantineConsistency.Sign14Positive74ObjectCoordinateElim.listConjElim
#print axioms DiophantineConsistency.Sign14Positive74ObjectCoordinateElim.nonzeroAt
#print axioms DiophantineConsistency.Sign14Positive74ObjectCoordinateElim.reconstructionAt
