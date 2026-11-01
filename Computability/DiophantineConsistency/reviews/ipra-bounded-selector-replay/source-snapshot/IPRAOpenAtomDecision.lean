import DiophantineConsistency.IPRANativeOpenDecision
import DiophantineConsistency.IPRAStableBackward
/-! Open NNF formulas admit native decision and GG-to-native transfer when
each of their actual atoms is explicitly decidable. No general equality
decision or bounded-search principle is assumed or proved here. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.IPRAOpenAtomDecision
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRANativeOpenDecision
open DiophantineConsistency.IPRANativeFormula
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def AtomDecisions : Proposition language → Prop
  | .rel r v => extended nativeTheory ⊢ native (.rel r v) ⋎ ∼native (.rel r v)
  | .nrel r v => extended nativeTheory ⊢ native (.rel r v) ⋎ ∼native (.rel r v)
  | ⊤ => True
  | ⊥ => True
  | φ ⋏ ψ => AtomDecisions φ ∧ AtomDecisions ψ
  | φ ⋎ ψ => AtomDecisions φ ∧ AtomDecisions ψ
  | ∀⁰ _ => False
  | ∃⁰ _ => False

def decision : (φ : Proposition language) → AtomDecisions φ →
    extended nativeTheory ⊢! native φ ⋎ ∼native φ
  | .rel r v, h => by
    simp only [AtomDecisions.eq_1, AtomDecisions.eq_2, AtomDecisions.eq_5, AtomDecisions.eq_6, AtomDecisions.eq_7, AtomDecisions.eq_8] at h
    exact Classical.choice h
  | .nrel r v, h => by
    simp only [AtomDecisions.eq_1, AtomDecisions.eq_2, AtomDecisions.eq_5, AtomDecisions.eq_6, AtomDecisions.eq_7, AtomDecisions.eq_8] at h
    exact (decNeg (native (.rel r v))) ⨀ Classical.choice h
  | ⊤, _ => Entailment.A_intro_left HilbertProofᵢ.verum
  | ⊥, _ => Entailment.A_intro_right Entailment.C_id
  | φ ⋏ ψ, h => by
    change AtomDecisions (.and φ ψ) at h
    rw [AtomDecisions.eq_5] at h
    exact decAnd (native φ) (native ψ) ⨀ decision φ h.1 ⨀ decision ψ h.2
  | φ ⋎ ψ, h => by
    change AtomDecisions (.or φ ψ) at h
    rw [AtomDecisions.eq_6] at h
    exact decOr (native φ) (native ψ) ⨀ decision φ h.1 ⨀ decision ψ h.2
  | ∀⁰ φ, h => by
    change AtomDecisions (.all φ) at h
    rw [AtomDecisions.eq_7] at h
    exact False.elim h
  | ∃⁰ φ, h => by
    change AtomDecisions (.exs φ) at h
    rw [AtomDecisions.eq_8] at h
    exact False.elim h
  termination_by φ _ => φ.complexity

def backward : (φ : Proposition language) → AtomDecisions φ →
    extended nativeTheory ⊢! φᴺ 🡒 native φ
  | .rel r v, h => by
    simp only [AtomDecisions.eq_1, AtomDecisions.eq_2, AtomDecisions.eq_5, AtomDecisions.eq_6, AtomDecisions.eq_7, AtomDecisions.eq_8] at h
    exact stableOfDec (native (.rel r v)) (Classical.choice h)
  | .nrel _ _, _ => Entailment.C_id
  | ⊤, _ => Entailment.C_id
  | ⊥, _ => Entailment.C_id
  | φ ⋏ ψ, h => by
    change AtomDecisions (.and φ ψ) at h
    rw [AtomDecisions.eq_5] at h
    exact Entailment.CK_of_C_of_C
      (Entailment.C_trans Entailment.and₁ (backward φ h.1))
      (Entailment.C_trans Entailment.and₂ (backward ψ h.2))
  | φ ⋎ ψ, h => by
    have hh := h
    change AtomDecisions (.or φ ψ) at h
    rw [AtomDecisions.eq_6] at h
    have ha : extended nativeTheory ⊢! ∼(native φ ⋎ native ψ) 🡒 ∼φᴺ :=
      Entailment.C_trans (Entailment.contra Entailment.or₁)
        (Entailment.contra (backward φ h.1))
    have hb : extended nativeTheory ⊢! ∼(native φ ⋎ native ψ) 🡒 ∼ψᴺ :=
      Entailment.C_trans (Entailment.contra Entailment.or₂)
        (Entailment.contra (backward ψ h.2))
    exact Entailment.C_trans (Entailment.contra (Entailment.CK_of_C_of_C ha hb))
      (stableOfDec _ (decision (φ ⋎ ψ) hh))
  | ∀⁰ φ, h => by
    change AtomDecisions (.all φ) at h
    rw [AtomDecisions.eq_7] at h
    exact False.elim h
  | ∃⁰ φ, h => by
    change AtomDecisions (.exs φ) at h
    rw [AtomDecisions.eq_8] at h
    exact False.elim h
  termination_by φ _ => φ.complexity
end DiophantineConsistency.IPRAOpenAtomDecision
