import DiophantineConsistency.Sign14Positive74ObjectPredecessor

/-! SOURCE-ONLY: all fourteen native nonzero assumptions reconstruct successors. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectGuardReconstruct
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRAFiniteFunctionCodes IPRANativeTheory
open IPRATheoryHilbertBridge IPRANativeAtomStability Sign14Positive74ObjectPredecessor
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def mapConjImp {α : Type} (a b : α → Propositionᵢ language)
    (h : ∀ i, extended nativeTheory ⊢! (a i 🡒 b i)) :
    (xs : List α) → extended nativeTheory ⊢! ((⋀ (xs.map a)) 🡒 (⋀ (xs.map b)))
  | [] => by simpa using (Entailment.C_id (φ := (⊤ : Propositionᵢ language)))
  | [x] => by simpa using h x
  | x :: y :: xs => by
    have hr := mapConjImp a b h (y :: xs)
    have t : extended nativeTheory ⊢!
        ((a x 🡒 b x) 🡒 (((⋀ ((y :: xs).map a)) 🡒 (⋀ ((y :: xs).map b))) 🡒
          ((a x ⋏ ⋀ ((y :: xs).map a)) 🡒 (b x ⋏ ⋀ ((y :: xs).map b))))) := by
      apply Classical.choice
      change extended nativeTheory ⊢ _
      int_prover
    simpa only [List.map, List.conj₂] using (t ⨀ h x ⨀ hr)

def nonzeroGuardOpen (v : Fin 14 → Term language ℕ) : Propositionᵢ language :=
  ⋀ ((List.finRange 14).map fun i => ∼eqAt (v i) zero)

def reconstructGuardOpen (v : Fin 14 → Term language ℕ) : Propositionᵢ language :=
  ⋀ ((List.finRange 14).map fun i => eqAt (v i) (succ (pred (v i))))

def allReconstructOpen (v : Fin 14 → Term language ℕ) :
    extended nativeTheory ⊢! (nonzeroGuardOpen v 🡒 reconstructGuardOpen v) := by
  exact mapConjImp _ _ (fun i => nonzeroReconstructionOpen (v i)) (List.finRange 14)
end DiophantineConsistency.Sign14Positive74ObjectGuardReconstruct
#print axioms DiophantineConsistency.Sign14Positive74ObjectGuardReconstruct.mapConjImp
#print axioms DiophantineConsistency.Sign14Positive74ObjectGuardReconstruct.allReconstructOpen
