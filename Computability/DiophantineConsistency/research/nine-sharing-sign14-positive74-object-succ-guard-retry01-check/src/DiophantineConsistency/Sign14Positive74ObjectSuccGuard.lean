import DiophantineConsistency.Sign14Positive74ObjectShiftMatrix

/-! SOURCE ONLY: native positivity guard for all successor assignments. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectSuccGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRANativeInduction IPRATheoryHilbertBridge
open IPRATheoryInstantiation IPRANativeAtomStability Sign14Positive74ObjectPredecessor
open Sign14Positive74ObjectGuardReconstruct Sign14Positive74ObjectGuardBind
open Sign14Positive74ObjectShiftPositiveLeaf
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def succNonzeroOpen (a : Term language ℕ) : extended nativeTheory ⊢!
    ∼eqAt (.func .succ (fun _ => a)) zero := by
  let m : Semisentenceᵢ language 1 :=
    ∼(Semiformulaᵢ.rel .eq ![.func .succ (fun _ => #0), zeroTerm 1])
  have ha : nativeTheory ⊢! ∀⁰* m := by
    simpa [m, succNonzeroI, applyCode, zeroTerm] using
      (Axiomatized.prfAxm (NativeAxiom.basic BasicAxiomI.succNonzero) : nativeTheory ⊢! succNonzeroI)
  have hp := instantiateTheory (T := nativeTheory) m ha ![a]
  have hv : (fun i : Fin 2 => (Rew.embSubsts ![a])
      (![.func .succ (fun _ => #0), zeroTerm 1] i)) =
        ![.func .succ (fun _ => a), zero] := by
    funext i; fin_cases i <;> simp [zeroTerm, zero, Rew.func, Function.comp_def, funext_iff]
  simpa [m, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp

def succGuardOpen (v : Fin 14 → Term language ℕ) : extended nativeTheory ⊢!
    (Rew.embSubsts (succVec v) ▹ Sign14Positive74ObjectGuard.guard) := by
  rw [guard_subst]
  apply Entailment.Conj₂_intro
  intro φ hφ
  apply Classical.choice
  change extended nativeTheory ⊢ φ
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hφ
  exact ⟨succNonzeroOpen (v i)⟩
end DiophantineConsistency.Sign14Positive74ObjectSuccGuard
#print axioms DiophantineConsistency.Sign14Positive74ObjectSuccGuard.succNonzeroOpen
#print axioms DiophantineConsistency.Sign14Positive74ObjectSuccGuard.succGuardOpen
