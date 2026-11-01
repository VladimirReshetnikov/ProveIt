import DiophantineConsistency.IPRAExistentialComparison
import DiophantineConsistency.IPRABoundedErasureLogic
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace DiophantineConsistency.IPRAStableBackward
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRANativeFormulaRew DiophantineConsistency.IPRAExistentialComparison
open DiophantineConsistency.IPRABoundedErasureLogic
variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

/-- Cases where the structural argument uses native double-negation stability. -/
def NeedsStability : Proposition L → Prop
  | .rel _ _ => True
  | .or _ _ => True
  | .exs _ => True
  | _ => False

/-- A syntax set closed under the recursive obligations generated below. -/
structure Support (P : Proposition L → Prop) : Prop where
  and_left : ∀ {φ ψ}, P (φ ⋏ ψ) → P φ
  and_right : ∀ {φ ψ}, P (φ ⋏ ψ) → P ψ
  or_left : ∀ {φ ψ}, P (φ ⋎ ψ) → P φ
  or_right : ∀ {φ ψ}, P (φ ⋎ ψ) → P ψ
  all_free : ∀ {φ : Semiproposition L 1}, P (∀⁰ φ) → P (free φ)
  exs_free : ∀ {φ : Semiproposition L 1}, P (∃⁰ φ) → P (free φ)

/-- GG implies the native NNF reader when all selected relevant positive
atoms, disjunctions and existentials are stable. -/
noncomputable def nativeBackward (P : Proposition L → Prop) (closed : Support P)
    (stable : ∀ ψ : Proposition L, P ψ → NeedsStability ψ → Λ ⊢! ∼∼native ψ 🡒 native ψ) :
    (φ : Proposition L) → P φ → Λ ⊢! φᴺ 🡒 native φ
  | .rel r v, h => stable (.rel r v) h trivial
  | .nrel r v, _ => Entailment.C_id
  | ⊤, _ => Entailment.C_id
  | ⊥, _ => Entailment.C_id
  | φ ⋏ ψ, h =>
    Entailment.CK_of_C_of_C
      (Entailment.C_trans Entailment.and₁ (nativeBackward P closed stable φ (closed.and_left h)))
      (Entailment.C_trans Entailment.and₂ (nativeBackward P closed stable ψ (closed.and_right h)))
  | φ ⋎ ψ, h => by
    have ha : Λ ⊢! ∼(native φ ⋎ native ψ) 🡒 ∼φᴺ :=
      Entailment.C_trans (Entailment.contra Entailment.or₁)
        (Entailment.contra (nativeBackward P closed stable φ (closed.or_left h)))
    have hb : Λ ⊢! ∼(native φ ⋎ native ψ) 🡒 ∼ψᴺ :=
      Entailment.C_trans (Entailment.contra Entailment.or₂)
        (Entailment.contra (nativeBackward P closed stable ψ (closed.or_right h)))
    exact Entailment.C_trans (Entailment.contra (Entailment.CK_of_C_of_C ha hb)) (stable (φ ⋎ ψ) h trivial)
  | ∀⁰ φ, h => by
    apply eraseAll
    have hh := nativeBackward P closed stable (free φ) (closed.all_free h)
    simpa only [native_rew, Semiformula.rew_doubleNegation] using hh
  | ∃⁰ φ, h => by
    have hh := nativeBackward P closed stable (free φ) (closed.exs_free h)
    have hc : Λ ⊢! free (φᴺ) 🡒 free (native φ) := by
      simpa only [native_rew, Semiformula.rew_doubleNegation] using hh
    exact Entailment.C_trans (existsCompare φ hc) (stable (∃⁰ φ) h trivial)
  termination_by φ _ => φ.complexity
end DiophantineConsistency.IPRAStableBackward
