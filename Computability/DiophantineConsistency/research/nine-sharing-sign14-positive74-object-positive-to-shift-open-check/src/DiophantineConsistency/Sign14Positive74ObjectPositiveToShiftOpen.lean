import DiophantineConsistency.Sign14Positive74ObjectSuccGuard

/-! SOURCE ONLY: specialize guarded sentence to successor assignments. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectPositiveToShiftOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge IPRATheoryInstantiation
open AdaptiveEquationSyntax2011 Sign14Positive74ObjectGuard Sign14Positive74ObjectMatrixGuard
open Sign14Positive74ObjectShiftPositiveLeaf Sign14Positive74ObjectShiftMatrix Sign14Positive74ObjectSuccGuard
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def positiveToShiftOpen (e : Expr (Fin 14)) (v : Fin 14 → Term language ℕ) :
    extended nativeTheory ⊢!
      (Rew.emb (positiveNoZero e) 🡒 ∼(Rew.embSubsts v ▹ equalityMatrix (positiveShift e))) := by
  let m : Semisentenceᵢ language 14 := guard 🡒 ∼equalityMatrix e
  have he : (Rew.subst (succVec v)).comp Rew.emb = Rew.embSubsts (succVec v) := by
    ext x
    · simp [Rew.comp_app]
    · exact Empty.elim x
  have hi := allInst (Λ := extended nativeTheory) (Rew.emb ▹ m) (succVec v)
  have hs0 : extended nativeTheory ⊢!
      (Rew.emb (∀⁰* m) 🡒 (Rew.embSubsts (succVec v) ▹ m)) := by
    simpa only [Rewriting.emb_allClosure, ← TransitiveRewriting.comp_app, he] using hi
  have hs : extended nativeTheory ⊢!
      (Rew.emb (positiveNoZero e) 🡒
        ((Rew.embSubsts (succVec v) ▹ guard) 🡒 ∼(Rew.embSubsts (succVec v) ▹ equalityMatrix e))) := by
    change extended nativeTheory ⊢! (Rew.emb (∀⁰* m) 🡒
      ((Rew.embSubsts (succVec v) ▹ guard) 🡒 ∼(Rew.embSubsts (succVec v) ▹ equalityMatrix e)))
    simpa only [m, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg] using hs0
  have hlogic : extended nativeTheory ⊢!
      ((Rew.emb (positiveNoZero e) 🡒
        ((Rew.embSubsts (succVec v) ▹ guard) 🡒 ∼(Rew.embSubsts (succVec v) ▹ equalityMatrix e))) 🡒
        (Rew.embSubsts (succVec v) ▹ guard) 🡒
          (Rew.emb (positiveNoZero e) 🡒 ∼(Rew.embSubsts (succVec v) ▹ equalityMatrix e))) := by
    apply Classical.choice
    change extended nativeTheory ⊢ _
    int_prover
  exact Entailment.C_trans (hlogic ⨀ hs ⨀ succGuardOpen v) (Entailment.contra (shiftForward v e))
end DiophantineConsistency.Sign14Positive74ObjectPositiveToShiftOpen
#print axioms DiophantineConsistency.Sign14Positive74ObjectPositiveToShiftOpen.positiveToShiftOpen
