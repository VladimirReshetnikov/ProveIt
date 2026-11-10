import DiophantineConsistency.Sign14Positive74ObjectMultiSubst

/-! SOURCE-ONLY: 14-coordinate native substitution under actual guard. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectGuardedSubst
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage IPRANativeTheory IPRATheoryHilbertBridge
open Sign14Positive74ObjectPredecessor Sign14Positive74ObjectGuardReconstruct
open Sign14Positive74ObjectCoordinateElim Sign14Positive74ObjectGuardBind

def predSuccVec (v : Fin 14 → Term language ℕ) : Fin 14 → Term language ℕ :=
  fun i => succ (pred (v i))

def guardedSubstitution (φ : Semisentenceᵢ language 14) (v : Fin 14 → Term language ℕ) :
    extended nativeTheory ⊢!
      ((Rew.embSubsts v ▹ Sign14Positive74ObjectGuard.guard) 🡒
        ((Rew.embSubsts v ▹ φ) 🡒 (Rew.embSubsts (predSuccVec v) ▹ φ))) := by
  have h := Sign14Positive74ObjectMultiSubst.guardedAllSubstitution φ v (predSuccVec v)
    (nonzeroGuardOpen v) (fun i => reconstructionAt v i)
  simpa only [guard_subst] using h
end DiophantineConsistency.Sign14Positive74ObjectGuardedSubst
#print axioms DiophantineConsistency.Sign14Positive74ObjectGuardedSubst.guardedSubstitution
