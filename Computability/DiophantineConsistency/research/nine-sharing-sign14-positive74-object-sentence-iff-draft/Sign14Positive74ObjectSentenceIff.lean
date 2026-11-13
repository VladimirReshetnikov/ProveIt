import DiophantineConsistency.Sign14Positive74ObjectCloseImp

/-! SOURCE ONLY: close the two actual native object-language directions. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectSentenceIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRAExpressionNative AdaptiveEquationSyntax2011
open Sign14Positive74ObjectGuard Sign14Positive74ObjectMatrixGuard
open Sign14Positive74ObjectPositiveToShiftOpen Sign14Positive74ObjectShiftToPositiveOpen
open Sign14Positive74ObjectCloseBind Sign14Positive74ObjectCloseImp
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def guardedToShift (e : Expr (Fin 14)) : nativeTheory ⊢!
    (positiveNoZero e 🡒 nativeNoZero (positiveShift e)) := by
  apply closeImp14 (positiveNoZero e) (∼equalityMatrix (positiveShift e))
  simpa only [LogicalConnective.HomClass.map_neg] using positiveToShiftOpen e freeVec

def shiftToGuarded (e : Expr (Fin 14)) : nativeTheory ⊢!
    (nativeNoZero (positiveShift e) 🡒 positiveNoZero e) := by
  apply closeImp14 (nativeNoZero (positiveShift e)) (guard 🡒 ∼equalityMatrix e)
  simpa only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg] using
    shiftToPositiveOpen e freeVec

def sentenceIff (e : Expr (Fin 14)) : nativeTheory ⊢!
    (positiveNoZero e 🡘 nativeNoZero (positiveShift e)) :=
  Entailment.K_intro (guardedToShift e) (shiftToGuarded e)
end DiophantineConsistency.Sign14Positive74ObjectSentenceIff
#print axioms DiophantineConsistency.Sign14Positive74ObjectSentenceIff.guardedToShift
#print axioms DiophantineConsistency.Sign14Positive74ObjectSentenceIff.shiftToGuarded
#print axioms DiophantineConsistency.Sign14Positive74ObjectSentenceIff.sentenceIff
