import DiophantineConsistency.Sign14Positive74ObjectCoordinateFocus

/-! SOURCE-ONLY: native one-coordinate substitution at an arbitrary index. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectCoordinateNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRANativeAtomStability
open IPRATheoryHilbertBridge Sign14Positive74ObjectCoordinateFocus

def updateOpen {n : ℕ} (φ : Semisentenceᵢ language (n+1)) (v : Fin (n+1) → Term language ℕ)
    (i : Fin (n+1)) (y : Term language ℕ) :
    extended nativeTheory ⊢! (eqAt (v i) y 🡒
      ((Rew.embSubsts v ▹ φ) 🡒 (Rew.embSubsts (Function.update v i y) ▹ φ))) := by
  have h := Sign14Positive74ObjectLeibnizParamNative.substitutionOpen
    (focusFormula i φ) (v i) y (i.removeNth v)
  have hv : Function.update v i (v i) = v := by
    funext j
    by_cases hji : j = i <;> simp [hji]
  simpa only [focus_subst, hv] using h
end DiophantineConsistency.Sign14Positive74ObjectCoordinateNative
#print axioms DiophantineConsistency.Sign14Positive74ObjectCoordinateNative.updateOpen
