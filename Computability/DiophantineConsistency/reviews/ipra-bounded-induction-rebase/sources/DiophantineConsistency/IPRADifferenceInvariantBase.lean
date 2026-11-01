import DiophantineConsistency.IPRADifferenceInvariant
import DiophantineConsistency.IPRASubArithmetic
import DiophantineConsistency.IPRAEqualitySymmetryGG
import Foundation.Meta.IntProver
/-! Native base case for the two-difference induction invariant. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRADifferenceInvariantBase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeInduction DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
open DiophantineConsistency.IPRADifferenceInvariant DiophantineConsistency.IPRANativeDifferenceEquality
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRAAllSpecialize
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def zeroMatrix : Semisentenceᵢ language 1 := .rel .eq ![#0, zeroTerm 1]

def leibZero (x y : Term language ℕ) : extended nativeTheory ⊢!
    eqAt x y 🡒 (zeroOpen x 🡒 zeroOpen y) := by
  have ha : nativeTheory ⊢! eqSubstitutionI zeroMatrix :=
    Axiomatized.prfAxm (NativeAxiom.equality (EqualityAxiomI.substitution zeroMatrix))
  have hp := instantiateTheory (T := nativeTheory) (leibnizBody zeroMatrix) ha ![x,y]
  have hv : (Rew.embSubsts ![x,y] ▹ leibnizBody zeroMatrix) =
      (eqAt x y 🡒 (zeroOpen x 🡒 zeroOpen y)) := by
    simp [leibnizBody, eqLeft, eqRight, zeroMatrix, eqAt, zeroOpen, zeroTerm,
      Semiformulaᵢ.rew_rel]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; try (funext k; exact Fin.elim0 k)
      | succ j => exact Fin.elim0 j
  rw [hv] at hp
  exact hp

def subZeroOpen (y : Term language ℕ) : extended nativeTheory ⊢!
    eqAt (.func subCode ![y, .func (Code.zero 0) Fin.elim0]) y := by
  let m : Semisentenceᵢ language 1 := .rel .eq ![.func subCode ![#0, zeroTerm 1],#0]
  have hp := instantiateTheory (T := nativeTheory) m (Classical.choice DiophantineConsistency.IPRASubArithmetic.sub_zero_native) ![y]
  have hv : (fun i : Fin 2 => Rew.embSubsts ![y] (![.func subCode ![#0, zeroTerm 1],#0] i)) =
      ![.func subCode ![y,.func (Code.zero 0) Fin.elim0],y] := by
    funext i
    cases i using Fin.cases with
    | zero =>
      simp [zeroTerm, Rew.func, Function.comp_def]
      funext k; cases k using Fin.cases with
      | zero =>
        change (Rew.embSubsts ![y]) (#(0 : Fin 1)) = y
        simp
      | succ j => cases j using Fin.cases with
        | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  simpa [m, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp

def symmetryZero (y : Term language ℕ) : extended nativeTheory ⊢!
    zeroOpen y 🡒 eqAt (.func (Code.zero 0) Fin.elim0) y := by
  let m : Semisentenceᵢ language 2 := .rel .eq ![#1,#0] 🡒 .rel .eq ![#0,#1]
  have hp := instantiateTheory (T := nativeTheory) m (Classical.choice DiophantineConsistency.IPRAEqualitySymmetryGG.symmetry_native)
    ![.func (Code.zero 0) Fin.elim0,y]
  have hv1 : (fun i : Fin 2 => Rew.embSubsts ![.func (Code.zero 0) Fin.elim0,y] (![#1,#0] i)) =
      ![y, .func (Code.zero 0) Fin.elim0] := by
    funext i; cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have hv2 : (fun i : Fin 2 => Rew.embSubsts ![.func (Code.zero 0) Fin.elim0,y] (![#0,#1] i)) =
      ![.func (Code.zero 0) Fin.elim0,y] := by
    funext i; cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  simpa [m, zeroOpen, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv1, hv2] using hp
def baseOpen (y : Term language ℕ) : extended nativeTheory ⊢!
    Rew.embSubsts ![y] ▹ atZero invariant := by
  let z : Term language ℕ := .func (Code.zero 0) Fin.elim0
  let a := zeroOpen y
  let b := zeroOpen (.func subCode ![y,z])
  let c := eqAt z y
  let d := zeroOpen (.func subCode ![z,y])
  have hd : extended nativeTheory ⊢! a ⋎ ∼a :=
    zeroDecOpen (Classical.choice DiophantineConsistency.IPRAZeroStepNative.zero_decidable) y
  have hs := symmetryZero y
  have hz := subZeroOpen y
  have hl := leibZero (.func subCode ![y,z]) y
  have hc : extended nativeTheory ⊢! c 🡒 (∼d ⋎ (∼b ⋎ c)) :=
    Entailment.C_trans Entailment.or₂ Entailment.or₂
  have hn : extended nativeTheory ⊢! ∼b 🡒 (∼d ⋎ (∼b ⋎ c)) :=
    Entailment.C_trans Entailment.or₁ Entailment.or₂
  have hres : extended nativeTheory ⊢! ∼d ⋎ (∼b ⋎ c) :=
    Entailment.of_C_of_C_of_A (Entailment.C_trans hs hc)
      (Entailment.C_trans (Entailment.contra (hl ⨀ hz)) hn) hd
  let r : Rew language Empty 2 ℕ 0 := (Rew.embSubsts ![y]).comp (Rew.subst (Fin.cases (zeroTerm 1) (fun _ => #0)))
  have hvec1 : (fun i : Fin 2 => r (![.func subCode ![#0,#1], zeroTerm 2] i)) =
      ![.func subCode ![z,y], z] := by
    funext i
    cases i using Fin.cases with
    | zero =>
      simp [r, Rew.comp_app, Rew.func, zeroTerm, z, Function.comp_def]
      funext j; cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => cases j using Fin.cases with
        | zero =>
          change (Rew.embSubsts ![y]) (#(0 : Fin 1)) = y
          simp
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [r, Rew.comp_app, Rew.func, zeroTerm, z, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hvec2 : (fun i : Fin 2 => r (![.func subCode ![#1,#0], zeroTerm 2] i)) =
      ![.func subCode ![y,z], z] := by
    funext i
    cases i using Fin.cases with
    | zero =>
      simp [r, Rew.comp_app, Rew.func, zeroTerm, z, Function.comp_def]
      funext j; cases j using Fin.cases with
      | zero =>
        change (Rew.embSubsts ![y]) (#(0 : Fin 1)) = y
        simp
      | succ j => cases j using Fin.cases with
        | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [r, Rew.comp_app, Rew.func, zeroTerm, z, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hvec3 : (fun i : Fin 2 => r (![#0,#1] i)) = ![z,y] := by
    funext i; cases i using Fin.cases with
    | zero => simp [r, Rew.comp_app, Rew.func, zeroTerm, z, Function.comp_def]; funext k; exact Fin.elim0 k
    | succ j => cases j using Fin.cases with
      | zero =>
        change (Rew.embSubsts ![y]) (#(0 : Fin 1)) = y
        simp
      | succ j => exact Fin.elim0 j
  dsimp only [r] at hvec1 hvec2 hvec3
  have hv : Rew.embSubsts ![y] ▹ atZero invariant = ∼d ⋎ (∼b ⋎ c) := by
    simp [atZero, invariant, diff1, diff2, eqMatrix, zeroOpen, eqAt,
      Semiformulaᵢ.rew_rel, b, c, d, ← Rew.comp_app, hvec1, hvec2, hvec3]
    constructor <;> rfl
  rw [hv]
  exact hres

def base : nativeTheory ⊢! baseSentence := by
  have hv := baseOpen (&0)
  apply extendedToTheory nativeTheory
  simp only [baseSentence, allClosure_succ, allClosure_zero, Rewriting.app_all, Rew.q_emb]
  apply HilbertProofᵢ.gen
  change extended nativeTheory ⊢! _
  have hre : (Rew.free : Rew language ℕ 1 ℕ 0).comp (Rew.emb : Rew language Empty 1 ℕ 1) = Rew.embSubsts ![&0] := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ j => exact Fin.elim0 j
    · exact Empty.elim x
  change extended nativeTheory ⊢! Rew.free ▹ (Rew.emb ▹ atZero invariant)
  rw [← TransitiveRewriting.comp_app, hre]
  exact hv

/-- The native successor induction case is the only remaining premise. -/
def equalityDecidable (hstep : nativeTheory ⊢! stepSentence) : nativeTheory ⊢! eqDecSentence :=
  DiophantineConsistency.IPRADifferenceInvariant.equalityDecidable base hstep
end DiophantineConsistency.IPRADifferenceInvariantBase
