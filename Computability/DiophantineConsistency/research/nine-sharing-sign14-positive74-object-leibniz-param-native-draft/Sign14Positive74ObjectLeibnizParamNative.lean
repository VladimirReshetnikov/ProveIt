import DiophantineConsistency.Sign14Positive74ObjectLeibnizParam

/-! SOURCE-ONLY: native one-coordinate substitution with other parameters. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectLeibnizParamNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRAFiniteFunctionCodes IPRANativeTheory
open IPRATheoryHilbertBridge IPRATheoryInstantiation IPRANativeAtomStability
open Sign14Positive74ObjectLeibnizParam
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def substitutionOpen {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (x y : Term language ℕ) (v : Fin n → Term language ℕ) :
    extended nativeTheory ⊢! (eqAt x y 🡒
      ((Rew.embSubsts (Fin.cons x v) ▹ φ) 🡒 (Rew.embSubsts (Fin.cons y v) ▹ φ))) := by
  have ha : nativeTheory ⊢! ∀⁰* (IPRAAllSpecialize.leibnizBody φ) := by
    simpa [eqSubstitutionI, IPRAAllSpecialize.leibnizBody] using
      (Axiomatized.prfAxm (NativeAxiom.equality (EqualityAxiomI.substitution φ)) :
        nativeTheory ⊢! eqSubstitutionI φ)
  have hp := instantiateTheory (T := nativeTheory) (IPRAAllSpecialize.leibnizBody φ) ha
    (Fin.cons x (Fin.cons y v))
  have hv : (fun i : Fin 2 => (Rew.embSubsts (Fin.cons x (Fin.cons y v)))
      (![.bvar 0,.bvar 1] i)) = ![x,y] := by
    apply funext
    simp [Fin.forall_fin_two]
  simpa [IPRAAllSpecialize.leibnizBody, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel,
    Function.comp_def, hv, eqAt, left_rewrite, right_rewrite] using hp
end DiophantineConsistency.Sign14Positive74ObjectLeibnizParamNative
#print axioms DiophantineConsistency.Sign14Positive74ObjectLeibnizParamNative.substitutionOpen
