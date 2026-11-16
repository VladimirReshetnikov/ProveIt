import DiophantineConsistency.IPRAArithmeticTerms
import DiophantineConsistency.IPRAAddOneDirect
import DiophantineConsistency.IPRAEqualitySymmetryGG
import DiophantineConsistency.IPRANativeAtomStability

/-! Open instances of parameter replacement, add-one, and equality symmetry. -/
set_option autoImplicit false
noncomputable section

namespace DiophantineConsistency

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAFiniteFunctionCodes
open IPRANativeInduction IPRANativeTheory
open IPRATheoryHilbertBridge IPRATheoryInstantiation IPRAAllSpecialize
open IPRANativeAtomStability IPRADifferenceStepClosure IPRADifferenceSuccEq

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

namespace IPRASuccessorInductionConverse

def replaceParameterT {T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)}
    (heq : ∀ σ, EqualityAxiomI σ → T ⊢! σ) {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (u v : Term language ℕ) (args : Fin n → Term language ℕ) :
    extended T ⊢! eqAt u v 🡒
      ((Rew.embSubsts (Fin.cases u args) ▹ φ) 🡒 (Rew.embSubsts (Fin.cases v args) ▹ φ)) := by
  have ha : T ⊢! eqSubstitutionI φ := heq _ (EqualityAxiomI.substitution φ)
  let vars : Fin (n+2) → Term language ℕ := Fin.cases u (Fin.cases v args)
  have hp := instantiateTheory (T := T) (leibnizBody φ) ha vars
  have hL : (Rew.embSubsts vars).comp (Rew.subst (Fin.cases #0 (fun i => #i.succ.succ))) =
      Rew.embSubsts (Fin.cases u args) := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app, vars]
      | succ j => simp [Rew.comp_app, vars]
    · exact Empty.elim i
  have varsOne : vars ((0 : Fin (n+1)).succ) = v := by
    dsimp only [vars]
    rw [Fin.cases_succ, Fin.cases_zero]
  have hR : (Rew.embSubsts vars).comp (Rew.subst (Fin.cases #1 (fun i => #i.succ.succ))) =
      Rew.embSubsts (Fin.cases v args) := by
    ext i
    · cases i using Fin.cases with
      | zero =>
        change vars ((0 : Fin (n+1)).succ) = v
        exact varsOne
      | succ j => simp [Rew.comp_app, vars]
    · exact Empty.elim i
  have he : (fun i : Fin 2 => Rew.embSubsts vars (![#0,#1] i)) = ![u,v] := by
    funext i; cases i using Fin.cases with
    | zero => simp [vars]
    | succ j => cases j using Fin.cases with
      | zero =>
        change vars ((0 : Fin (n+1)).succ) = v
        exact varsOne
      | succ j => exact Fin.elim0 j
  simpa only [leibnizBody, eqLeft, eqRight, LogicalConnective.HomClass.map_imply,
    ← TransitiveRewriting.comp_app, hL, hR, Semiformulaᵢ.rew_rel, he, eqAt] using hp
def addOneOpenT {T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)}
    (hadd : T ⊢ DiophantineConsistency.IPRAAddOneDirect.addOneI) (x : Term language ℕ) : extended T ⊢! eqAt (addOneTerm x) (sx x) := by
  let m : Semisentenceᵢ language 1 := .rel .eq ![stepTerm 0, .func Code.succ (fun _ => #0)]
  have hp := instantiateTheory (T := T) m (Classical.choice hadd) ![x]
  have hv : (fun i : Fin 2 => Rew.embSubsts ![x] (![stepTerm 0, .func Code.succ (fun _ => #0)] i)) =
      ![addOneTerm x,sx x] := by
    funext i; cases i using Fin.cases with
    | zero =>
      simp [stepTerm, addOneTerm, Rew.func, Function.comp_def]
      funext j; cases j using Fin.cases with
      | zero => simp
      | succ j => cases j using Fin.cases with
        | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def, sx]
      | succ j => exact Fin.elim0 j
  simpa [m, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp

end IPRASuccessorInductionConverse

namespace IPRADifferenceStepClosure

def addOneOpen (x : Term language ℕ) :
    extended nativeTheory ⊢! eqAt (addOneTerm x) (sx x) :=
  IPRASuccessorInductionConverse.addOneOpenT IPRAAddOneDirect.add_one_native x

def symmetryOpen (x y : Term language ℕ) : extended nativeTheory ⊢! eqAt x y 🡒 eqAt y x := by
  let m : Semisentenceᵢ language 2 := .rel .eq ![#1,#0] 🡒 .rel .eq ![#0,#1]
  have hp := instantiateTheory (T := nativeTheory) m (Classical.choice DiophantineConsistency.IPRAEqualitySymmetryGG.symmetry_native) ![y,x]
  have hv1 : (fun i : Fin 2 => Rew.embSubsts ![y,x] (![#1,#0] i)) = ![x,y] := by
    funext i; cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have hv2 : (fun i : Fin 2 => Rew.embSubsts ![y,x] (![#0,#1] i)) = ![y,x] := by
    funext i; cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  simpa [m, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv1, hv2] using hp

end IPRADifferenceStepClosure
end DiophantineConsistency
