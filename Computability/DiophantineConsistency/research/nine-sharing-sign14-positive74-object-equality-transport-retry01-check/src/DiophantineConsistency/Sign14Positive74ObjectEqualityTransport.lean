import DiophantineConsistency.Sign14Positive74ObjectShiftFull
import DiophantineConsistency.IPRADifferenceStepClosure

/-! SOURCE ONLY: native equality-atom transport from two native term equalities. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectEqualityTransport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge IPRANativeAtomStability
open Sign14Positive74ObjectLeibnizParamNative
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def equalityForward (a b c d : Term language ℕ)
    (hab : extended nativeTheory ⊢! eqAt a b) (hcd : extended nativeTheory ⊢! eqAt c d) :
    extended nativeTheory ⊢! (eqAt a c 🡒 eqAt b d) := by
  let left : Semisentenceᵢ language 2 := .rel .eq ![#0,#1]
  let right : Semisentenceᵢ language 2 := .rel .eq ![#1,#0]
  have hleft := substitutionOpen left a b ![c] ⨀ hab
  have hright := substitutionOpen right c d ![b] ⨀ hcd
  have hvL (x y : Term language ℕ) :
      (fun i : Fin 2 => (Rew.embSubsts ![x,y]) (![#0,#1] i)) = ![x,y] := by
    funext i; fin_cases i <;> simp
  have hvR (x y : Term language ℕ) :
      (fun i : Fin 2 => (Rew.embSubsts ![x,y]) (![#1,#0] i)) = ![y,x] := by
    funext i; fin_cases i <;> simp
  have h₁ : extended nativeTheory ⊢! (eqAt a c 🡒 eqAt b c) := by
    simpa [left, eqAt, Semiformulaᵢ.rew_rel, Function.comp_def, hvL] using hleft
  have h₂ : extended nativeTheory ⊢! (eqAt b c 🡒 eqAt b d) := by
    simpa [right, eqAt, Semiformulaᵢ.rew_rel, Function.comp_def, hvR] using hright
  exact Entailment.C_trans h₁ h₂

def equalityBackward (a b c d : Term language ℕ)
    (hab : extended nativeTheory ⊢! eqAt a b) (hcd : extended nativeTheory ⊢! eqAt c d) :
    extended nativeTheory ⊢! (eqAt b d 🡒 eqAt a c) :=
  equalityForward b a d c (IPRADifferenceStepClosure.symmetryOpen a b ⨀ hab)
    (IPRADifferenceStepClosure.symmetryOpen c d ⨀ hcd)
end DiophantineConsistency.Sign14Positive74ObjectEqualityTransport
#print axioms DiophantineConsistency.Sign14Positive74ObjectEqualityTransport.equalityForward
#print axioms DiophantineConsistency.Sign14Positive74ObjectEqualityTransport.equalityBackward
