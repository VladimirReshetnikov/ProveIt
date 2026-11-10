import DiophantineConsistency.Sign14Positive74ObjectGuardReconstruct

/-! SOURCE-ONLY: relate the instantiated closed guard to the open guard. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectGuardBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRAFiniteFunctionCodes IPRANativeTheory IPRANativeInduction
open IPRATheoryHilbertBridge IPRANativeAtomStability Sign14Positive74ObjectPredecessor
open Sign14Positive74ObjectGuardReconstruct

theorem guard_subst (v : Fin 14 → Term language ℕ) :
    Rew.embSubsts v ▹ Sign14Positive74ObjectGuard.guard = nonzeroGuardOpen v := by
  have hv (i : Fin 14) :
      (fun j : Fin 2 => (Rew.embSubsts v)
        (![.bvar i, .func (Code.zero 0) Fin.elim0] j)) = ![v i, zero] := by
    apply funext
    simp [Fin.forall_fin_two, zero, Rew.func, funext_iff]
  simp [Sign14Positive74ObjectGuard.guard, Sign14Positive74ObjectGuard.coordinateNonzero,
    nonzeroGuardOpen, List.finRange, List.map, List.conj₂, Semiformulaᵢ.rewAux,
    Semiformulaᵢ.rew_rel, Rew.func, Function.comp_def, hv, eqAt, zero]

def instantiatedGuardReconstructOpen (v : Fin 14 → Term language ℕ) :
    extended nativeTheory ⊢! ((Rew.embSubsts v ▹ Sign14Positive74ObjectGuard.guard) 🡒
      reconstructGuardOpen v) := by
  simpa only [guard_subst] using allReconstructOpen v
end DiophantineConsistency.Sign14Positive74ObjectGuardBind
#print axioms DiophantineConsistency.Sign14Positive74ObjectGuardBind.guard_subst
#print axioms DiophantineConsistency.Sign14Positive74ObjectGuardBind.instantiatedGuardReconstructOpen
