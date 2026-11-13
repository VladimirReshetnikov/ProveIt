import DiophantineConsistency.IPRAFoundationZFCQuantifiedStability
import Foundation.Meta.IntProver
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.IPRANativeDeepStability
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRANativeAtomCoverage
open DiophantineConsistency.IPRANativeOpenDecision DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeFormulaRew
open DiophantineConsistency.IPRAStableBackwardReach
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def stableNeg (a : Propositionᵢ language) : extended nativeTheory ⊢! ∼∼∼a 🡒 ∼a := by
  apply Classical.choice
  change extended nativeTheory ⊢ _
  int_prover

def stableTop : extended nativeTheory ⊢! ∼∼(⊤ : Propositionᵢ language) 🡒 ⊤ := by
  apply Classical.choice
  change extended nativeTheory ⊢ _
  int_prover

def stableBot : extended nativeTheory ⊢! ∼∼(⊥ : Propositionᵢ language) 🡒 ⊥ := Entailment.CNNOO

def stableAnd (a b : Propositionᵢ language)
    (ha : extended nativeTheory ⊢! ∼∼a 🡒 a)
    (hb : extended nativeTheory ⊢! ∼∼b 🡒 b) :
    extended nativeTheory ⊢! ∼∼(a ⋏ b) 🡒 a ⋏ b :=
  Entailment.CK_of_C_of_C
    (Entailment.C_trans (Entailment.CNNNN_of_C Entailment.and₁) ha)
    (Entailment.C_trans (Entailment.CNNNN_of_C Entailment.and₂) hb)

def stableOrLeft (a b : Propositionᵢ language)
    (hd : extended nativeTheory ⊢! a ⋎ ∼a)
    (hb : extended nativeTheory ⊢! ∼∼b 🡒 b) :
    extended nativeTheory ⊢! ∼∼(a ⋎ b) 🡒 a ⋎ b := by
  apply Entailment.FiniteContext.deduct'
  have hd' : [∼∼(a ⋎ b)] ⊢[extended nativeTheory]! a ⋎ ∼a := Entailment.FiniteContext.of hd
  apply Entailment.of_C_of_C_of_A ?_ ?_ hd'
  · exact Entailment.FiniteContext.of Entailment.or₁
  · apply Entailment.FiniteContext.deduct
    have hnnb : [∼a, ∼∼(a ⋎ b)] ⊢[extended nativeTheory]! ∼∼b := by
      apply Entailment.FiniteContext.deduct
      have hn : [∼b, ∼a, ∼∼(a ⋎ b)] ⊢[extended nativeTheory]! ∼(a ⋎ b) :=
        Entailment.NA_of_KNN (Entailment.K_intro Entailment.FiniteContext.byAxm₁ Entailment.FiniteContext.byAxm₀)
      exact Entailment.FiniteContext.byAxm₂ ⨀ hn
    exact Entailment.FiniteContext.of Entailment.or₂ ⨀ (Entailment.FiniteContext.of hb ⨀ hnnb)

def stableOrRight (a b : Propositionᵢ language)
    (hd : extended nativeTheory ⊢! b ⋎ ∼b)
    (ha : extended nativeTheory ⊢! ∼∼a 🡒 a) :
    extended nativeTheory ⊢! ∼∼(a ⋎ b) 🡒 a ⋎ b := by
  have hs : extended nativeTheory ⊢! (a ⋎ b) 🡒 (b ⋎ a) :=
    Entailment.left_A_intro Entailment.or₂ Entailment.or₁
  have hr : extended nativeTheory ⊢! (b ⋎ a) 🡒 (a ⋎ b) :=
    Entailment.left_A_intro Entailment.or₂ Entailment.or₁
  exact Entailment.C_trans (Entailment.CNNNN_of_C hs)
    (Entailment.C_trans (stableOrLeft b a hd ha) hr)

def stableAll (q : Semipropositionᵢ language 1)
    (h : extended nativeTheory ⊢! ∼∼free q 🡒 free q) :
    extended nativeTheory ⊢! ∼∼(∀⁰ q) 🡒 ∀⁰ q := by
  apply HilbertProofᵢ.implyAll
  have hs : extended nativeTheory ⊢! shift (∀⁰ q) 🡒 free q := by
    change HilbertProofᵢ (extended nativeTheory) (shift (∀⁰ q) 🡒 free q)
    simpa using HilbertProofᵢ.all₁ (Λ := extended nativeTheory) (shift q) (&0)
  have hd := Entailment.CNNNN_of_C hs
  have he : extended nativeTheory ⊢! shift (∼∼(∀⁰ q)) 🡒 ∼∼free q := by
    simpa only [LogicalConnective.HomClass.map_neg] using hd
  exact Entailment.C_trans he h

def DeepNeed : Proposition language → Prop
  | .or a b => ¬a.Open ∧ ¬b.Open
  | .exs _ => True
  | _ => False

def stableNative (heq : nativeTheory ⊢! eqDecSentence) (root : Proposition language)
    (needed : ∀ ψ, Reach root ψ → DeepNeed ψ → extended nativeTheory ⊢! ∼∼native ψ 🡒 native ψ) :
    (φ : Proposition language) → Reach root φ → extended nativeTheory ⊢! ∼∼native φ 🡒 native φ
  | .rel r v, _ => atomStable heq r v
  | .nrel r v, _ => stableNeg (Semiformulaᵢ.rel r v)
  | ⊤, _ => stableTop
  | ⊥, _ => stableBot
  | φ ⋏ ψ, h => stableAnd (native φ) (native ψ)
      (stableNative heq root needed φ (Reach.andLeft h)) (stableNative heq root needed ψ (Reach.andRight h))
  | φ ⋎ ψ, h => by
    classical
    by_cases hφ : φ.Open
    · exact stableOrLeft (native φ) (native ψ) (openDecision heq φ hφ)
        (stableNative heq root needed ψ (Reach.orRight h))
    · by_cases hψ : ψ.Open
      · exact stableOrRight (native φ) (native ψ) (openDecision heq ψ hψ)
          (stableNative heq root needed φ (Reach.orLeft h))
      · exact needed (φ ⋎ ψ) h ⟨hφ,hψ⟩
  | ∀⁰ φ, h => by
    apply stableAll
    have hh := stableNative heq root needed (free φ) (Reach.allFree h)
    simpa only [native_rew] using hh
  | ∃⁰ φ, h => needed (∃⁰ φ) h trivial
  termination_by φ _ => φ.complexity
end DiophantineConsistency.IPRANativeDeepStability
