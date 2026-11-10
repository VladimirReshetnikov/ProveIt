import DiophantineConsistency.Sign14Positive74ObjectPositiveToShiftOpen

/-! SOURCE ONLY: native shifted-to-guarded open implication. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectShiftToPositiveOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge IPRATheoryInstantiation
open IPRAExpressionNative AdaptiveEquationSyntax2011 Sign14Positive74ObjectGuard
open Sign14Positive74ObjectPredecessor Sign14Positive74ObjectGuardedSubst Sign14Positive74ObjectMatrixGuard
open Sign14Positive74ObjectShiftPositiveLeaf Sign14Positive74ObjectShiftMatrix
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def predVec (v : Fin 14 → Term language ℕ) : Fin 14 → Term language ℕ := fun i => pred (v i)

def shiftToPositiveOpen (e : Expr (Fin 14)) (v : Fin 14 → Term language ℕ) :
    extended nativeTheory ⊢!
      (Rewriting.emb (nativeNoZero (positiveShift e)) 🡒
        ((Rew.embSubsts v ▹ guard) 🡒 ∼(Rew.embSubsts v ▹ equalityMatrix e))) := by
  let m : Semisentenceᵢ language 14 := ∼equalityMatrix (positiveShift e)
  have he : (Rew.subst (predVec v)).comp Rew.emb = Rew.embSubsts (predVec v) := by
    ext x
    · simp [Rew.comp_app]
    · exact Empty.elim x
  have hi := allInst (Λ := extended nativeTheory) (Rew.emb ▹ m) (predVec v)
  have hs0 : extended nativeTheory ⊢!
      (Rewriting.emb (∀⁰* m) 🡒 (Rew.embSubsts (predVec v) ▹ m)) := by
    simpa only [Rewriting.emb_allClosure, ← TransitiveRewriting.comp_app, he] using hi
  have hs : extended nativeTheory ⊢!
      (Rewriting.emb (nativeNoZero (positiveShift e)) 🡒
        ∼(Rew.embSubsts (predVec v) ▹ equalityMatrix (positiveShift e))) := by
    change extended nativeTheory ⊢! (Rewriting.emb (∀⁰* m) 🡒
      ∼(Rew.embSubsts (predVec v) ▹ equalityMatrix (positiveShift e)))
    simpa only [m, LogicalConnective.HomClass.map_neg] using hs0
  have hv : succVec (predVec v) = predSuccVec v := rfl
  have hb : extended nativeTheory ⊢!
      ((Rew.embSubsts (predSuccVec v) ▹ equalityMatrix e) 🡒
        (Rew.embSubsts (predVec v) ▹ equalityMatrix (positiveShift e))) := by
    simpa only [hv] using shiftBackward (predVec v) e
  have ha := Entailment.C_trans hs (Entailment.contra hb)
  exact Entailment.C_trans ha (Entailment.C_swap (guardedContrapositive e v))
end DiophantineConsistency.Sign14Positive74ObjectShiftToPositiveOpen
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftToPositiveOpen.shiftToPositiveOpen
