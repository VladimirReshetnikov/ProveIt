import DiophantineConsistency.Sign14Positive74ObjectLeibnizRewrite

/-! SOURCE-ONLY: generic native unary Leibniz implication at open terms. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectLeibnizNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRAFiniteFunctionCodes IPRANativeTheory
open IPRATheoryHilbertBridge IPRATheoryInstantiation IPRANativeAtomStability
open Sign14Positive74ObjectLeibnizRewrite
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def substitutionOpen (φ : Semisentenceᵢ language 1) (x y : Term language ℕ) :
    extended nativeTheory ⊢! (eqAt x y 🡒
      ((Rew.embSubsts ![x] ▹ φ) 🡒 (Rew.embSubsts ![y] ▹ φ))) := by
  have ha : nativeTheory ⊢! ∀⁰* (IPRAAllSpecialize.leibnizBody φ) := by
    simpa [eqSubstitutionI, IPRAAllSpecialize.leibnizBody] using
      (Axiomatized.prfAxm (NativeAxiom.equality (EqualityAxiomI.substitution φ)) :
        nativeTheory ⊢! eqSubstitutionI φ)
  have hp := instantiateTheory (T := nativeTheory) (IPRAAllSpecialize.leibnizBody φ) ha ![x,y]
  have hv : (fun i : Fin 2 => (Rew.embSubsts ![x,y]) (![.bvar 0,.bvar 1] i)) = ![x,y] := by
    apply funext
    simp [Fin.forall_fin_two]
  simpa [IPRAAllSpecialize.leibnizBody, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel,
    Function.comp_def, hv, eqAt, left_rewrite, right_rewrite] using hp
end DiophantineConsistency.Sign14Positive74ObjectLeibnizNative
#print axioms DiophantineConsistency.Sign14Positive74ObjectLeibnizNative.substitutionOpen
