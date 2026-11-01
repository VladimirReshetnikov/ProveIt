import DiophantineConsistency.IPRADifferenceSuccLogic
import DiophantineConsistency.IPRAAddOneDirect
import DiophantineConsistency.IPRAEqualitySymmetryGG
/-! Close the native successor invariant using x+1, conditional on the positive branch. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRADifferenceStepClosure
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeInduction DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
open DiophantineConsistency.IPRADifferenceInvariant DiophantineConsistency.IPRANativeDifferenceEquality
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRAAllSpecialize
open DiophantineConsistency.IPRADifferenceSuccEq DiophantineConsistency.IPRADifferenceSuccLogic
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def replaceOne (φ : Semisentenceᵢ language 2) (u v y : Term language ℕ) :
    extended nativeTheory ⊢! eqAt u v 🡒
      ((Rew.embSubsts ![u,y] ▹ φ) 🡒 (Rew.embSubsts ![v,y] ▹ φ)) := by
  have ha : nativeTheory ⊢! eqSubstitutionI φ :=
    Axiomatized.prfAxm (NativeAxiom.equality (EqualityAxiomI.substitution φ))
  have hp := instantiateTheory (T := nativeTheory) (leibnizBody φ) ha ![u,v,y]
  have hL : (Rew.embSubsts ![u,v,y]).comp (Rew.subst (Fin.cases #0 (fun i => #i.succ.succ))) = Rew.embSubsts ![u,y] := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ j => cases j using Fin.cases with
        | zero =>
          change (Rew.embSubsts ![u,v,y]) (#(2 : Fin 3)) = y
          simp
        | succ j => exact Fin.elim0 j
    · exact Empty.elim i
  have hR : (Rew.embSubsts ![u,v,y]).comp (Rew.subst (Fin.cases #1 (fun i => #i.succ.succ))) = Rew.embSubsts ![v,y] := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ j => cases j using Fin.cases with
        | zero =>
          change (Rew.embSubsts ![u,v,y]) (#(2 : Fin 3)) = y
          simp
        | succ j => exact Fin.elim0 j
    · exact Empty.elim i
  have he : (fun i : Fin 2 => Rew.embSubsts ![u,v,y] (![#0,#1] i)) = ![u,v] := by
    funext i; cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  simpa only [leibnizBody, eqLeft, eqRight, LogicalConnective.HomClass.map_imply,
    ← TransitiveRewriting.comp_app, hL, hR, Semiformulaᵢ.rew_rel, he, eqAt] using hp
def addOneTerm (x : Term language ℕ) : Term language ℕ := .func addCode ![x, .func oneCode Fin.elim0]
def addOneOpen (x : Term language ℕ) : extended nativeTheory ⊢! eqAt (addOneTerm x) (sx x) := by
  let m : Semisentenceᵢ language 1 := .rel .eq ![stepTerm 0, .func Code.succ (fun _ => #0)]
  have hp := instantiateTheory (T := nativeTheory) m (Classical.choice DiophantineConsistency.IPRAAddOneDirect.add_one_native) ![x]
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

def invariantReplace (x y : Term language ℕ) : extended nativeTheory ⊢!
    (Rew.embSubsts ![sx x,y] ▹ invariant) 🡒 (Rew.embSubsts ![addOneTerm x,y] ▹ invariant) := by
  have he := (symmetryOpen (addOneTerm x) (sx x)) ⨀ addOneOpen x
  exact (replaceOne invariant (sx x) (addOneTerm x) y) ⨀ he

theorem invariantShape (x y : Term language ℕ) :
    (Rew.embSubsts ![x,y] ▹ invariant) =
      (∼zeroOpen (.func subCode ![x,y]) ⋎ (∼zeroOpen (.func subCode ![y,x]) ⋎ eqAt x y)) := by
  have he : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![#0,#1] i)) = ![x,y] := by
    funext i; cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have heswap : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![#1,#0] i)) = ![y,x] := by
    funext i; cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have hf1 : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![.func subCode ![#0,#1], zeroTerm 2] i)) =
      ![.func subCode ![x,y], .func (Code.zero 0) Fin.elim0] := by
    funext i; cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, he]
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hf2 : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![.func subCode ![#1,#0], zeroTerm 2] i)) =
      ![.func subCode ![y,x], .func (Code.zero 0) Fin.elim0] := by
    funext i; cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, heswap]
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simp [invariant, diff1, diff2, eqMatrix, zeroOpen, eqAt, Semiformulaᵢ.rew_rel, he, hf1, hf2]

def stepAddOpen (x y : Term language ℕ)
    (hbridge : extended nativeTheory ⊢! zeroOpen (.func subCode ![y,sx x]) 🡒
      (∼zeroOpen (.func subCode ![y,x]) 🡒 eqAt (sx x) y)) :
    extended nativeTheory ⊢! (Rew.embSubsts ![x,y] ▹ invariant) 🡒
      (Rew.embSubsts ![addOneTerm x,y] ▹ invariant) := by
  have hs : extended nativeTheory ⊢! (Rew.embSubsts ![x,y] ▹ invariant) 🡒
      (Rew.embSubsts ![sx x,y] ▹ invariant) := by
    simpa only [invariantShape] using stepOpen x y hbridge
  exact Entailment.C_trans hs (invariantReplace x y)

theorem stepRewrite (x y : Term language ℕ) :
    (Rew.embSubsts ![x,y] ▹ atStep invariant) = (Rew.embSubsts ![addOneTerm x,y] ▹ invariant) := by
  have hr : (Rew.embSubsts ![x,y]).comp (Rew.subst (Fin.cases (stepTerm 1) (fun i => #i.succ))) =
      Rew.embSubsts ![addOneTerm x,y] := by
    ext i
    · cases i using Fin.cases with
      | zero =>
        simp [Rew.comp_app, Rew.func, stepTerm, addOneTerm, Function.comp_def]
        funext j; cases j using Fin.cases with
        | zero => simp
        | succ j => cases j using Fin.cases with
          | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
          | succ j => exact Fin.elim0 j
      | succ j => cases j using Fin.cases with
        | zero =>
          change (Rew.embSubsts ![x,y]) (#(1 : Fin 2)) = y
          simp
        | succ j => exact Fin.elim0 j
    · exact Empty.elim i
  simp only [atStep, ← TransitiveRewriting.comp_app, hr]

def closedStep
    (hbridge : ∀ x y : Term language ℕ, extended nativeTheory ⊢! zeroOpen (.func subCode ![y,sx x]) 🡒
      (∼zeroOpen (.func subCode ![y,x]) 🡒 eqAt (sx x) y)) :
    nativeTheory ⊢! stepSentence := by
  have hs := stepAddOpen (&0) (&1) (hbridge (&0) (&1))
  apply extendedToTheory nativeTheory
  simp only [stepSentence, allClosure_succ, allClosure_zero, Rewriting.app_all, Rew.q_emb]
  apply HilbertProofᵢ.gen
  apply HilbertProofᵢ.gen
  change extended nativeTheory ⊢! _
  have hmap : ((Rew.free : Rew language ℕ 1 ℕ 0).comp
      (Rew.free : Rew language ℕ 1 ℕ 0).q).comp (Rew.emb : Rew language Empty 2 ℕ 2) =
      Rew.embSubsts ![&0,&1] := by
    ext i
    · cases i using Fin.cases with
      | zero => simp [Rew.comp_app, Rew.free_bvar_castSucc_zero, Rew.free_bvar_last_zero]
      | succ j => cases j using Fin.cases with
        | zero =>
          change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
          rw [Rew.free_bvar_last, Rew.free_fvar]
        | succ j => exact Fin.elim0 j
    · exact Empty.elim i
  change extended nativeTheory ⊢! Rew.free ▹ ((Rew.free : Rew language ℕ 1 ℕ 0).q ▹ (Rew.emb ▹ (invariant 🡒 atStep invariant)))
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app, hmap]
  rw [LogicalConnective.HomClass.map_imply, stepRewrite]
  exact hs

/-- Equality decidability follows once the positive open branch is supplied. -/
def equalityDecidable
    (hbridge : ∀ x y : Term language ℕ, extended nativeTheory ⊢! zeroOpen (.func subCode ![y,sx x]) 🡒
      (∼zeroOpen (.func subCode ![y,x]) 🡒 eqAt (sx x) y)) :
    nativeTheory ⊢! eqDecSentence :=
  DiophantineConsistency.IPRADifferenceInvariantBase.equalityDecidable (closedStep hbridge)
end DiophantineConsistency.IPRADifferenceStepClosure
