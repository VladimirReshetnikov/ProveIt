import DiophantineConsistency.IPRADifferenceEqualityZeroJoin
import DiophantineConsistency.IPRANativeAxiomImage
import Foundation.Meta.IntProver
/-! The exact open induction invariant for positive two-difference correctness. Its arithmetic base and successor cases remain explicit proof premises. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiophantineConsistency.IPRADifferenceInvariant
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRAQuantifierFree DiophantineConsistency.IPRANativeInduction
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRANativeAxiomImage
open DiophantineConsistency.IPRANativeDifferenceEquality DiophantineConsistency.IPRANativeAtomStability
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def invariant : Semisentenceᵢ language 2 := ∼diff1 ⋎ (∼diff2 ⋎ eqMatrix)
theorem invariantOpen : OpenI invariant := by simp [invariant, diff1, diff2, eqMatrix, OpenI]
def baseSentence : Sentenceᵢ language := ∀⁰* (atZero invariant)
def stepSentence : Sentenceᵢ language := ∀⁰* (∀⁰ (invariant 🡒 atStep invariant))

def invariantAll (hbase : nativeTheory ⊢! baseSentence) (hstep : nativeTheory ⊢! stepSentence) :
    nativeTheory ⊢! ∀⁰* (∀⁰ invariant) := by
  have hind : nativeTheory ⊢! inductionAxiom invariant :=
    Axiomatized.prfAxm (NativeAxiom.induction ⟨1, invariant, invariantOpen, rfl⟩)
  have hi := instantiateTheory (T := nativeTheory) (inductionBody invariant) hind ![&0]
  have hb := instantiateTheory (T := nativeTheory) (atZero invariant) hbase ![&0]
  have hs := instantiateTheory (T := nativeTheory) (∀⁰ (invariant 🡒 atStep invariant)) hstep ![&0]
  have hv : extended nativeTheory ⊢! (Rew.embSubsts ![&0] ▹ (∀⁰ invariant)) := by
    exact hi ⨀ hb ⨀ hs
  apply extendedToTheory nativeTheory
  simp only [allClosure_succ, allClosure_zero, Rewriting.app_all, Rew.q_emb]
  apply HilbertProofᵢ.gen
  change extended nativeTheory ⊢! _
  simp only [Rewriting.free, Rewriting.app_all] at hv ⊢
  have hq : ((Rew.free : Rew language ℕ 1 ℕ 0).q).comp (Rew.emb : Rew language Empty 2 ℕ 2) = (Rew.embSubsts ![&0]).q := by
    ext x
    · cases x using Fin.cases with
      | zero => simp [Rew.comp_app]
      | succ j => cases j using Fin.cases with
        | zero =>
          change Rew.free (#(Fin.last 1) : Semiterm language ℕ 2) =
            (Rew.embSubsts ![&0]).q (#((0 : Fin 1).succ))
          rw [Rew.free_bvar_last, Rew.q_bvar_succ]
          simp
        | succ j => exact Fin.elim0 j
    · exact Empty.elim x
  rw [← TransitiveRewriting.comp_app, hq]
  exact hv

def reverseFromInvariant (hbase : nativeTheory ⊢! baseSentence) (hstep : nativeTheory ⊢! stepSentence) :
    nativeTheory ⊢! backwardSentence := by
  have hall : nativeTheory ⊢! ∀⁰* invariant := by
    simpa only [allClosure_succ, allClosure_zero] using invariantAll hbase hstep
  have hi := instantiateTheory (T := nativeTheory) invariant hall ![&0,&1]
  let x : Term language ℕ := &0
  let y : Term language ℕ := &1
  let a := zeroOpen (.func subCode ![x,y])
  let b := zeroOpen (.func subCode ![y,x])
  let c := eqAt x y
  have he : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![#0,#1] i)) = ![x,y] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have heswap : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![#1,#0] i)) = ![y,x] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have hf1 : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![.func subCode ![#0,#1], zeroTerm 2] i)) =
      ![.func subCode ![x,y], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, he]
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hf2 : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![.func subCode ![#1,#0], zeroTerm 2] i)) =
      ![.func subCode ![y,x], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, heswap]
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hio : extended nativeTheory ⊢! ∼a ⋎ (∼b ⋎ c) := by
    simpa [invariant, diff1, diff2, eqMatrix, zeroOpen, eqAt, a, b, c, x, y,
      Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, he, hf1, hf2] using hi
  have hl : extended nativeTheory ⊢! (∼a ⋎ (∼b ⋎ c)) 🡒 ((a ⋏ b) 🡒 c) := by
    apply Classical.choice
    change extended nativeTheory ⊢ _
    int_prover
  have ho := hl ⨀ hio
  apply extendedToTheory nativeTheory
  simp only [backwardSentence, allClosure_succ, allClosure_zero]
  apply HilbertProofᵢ.gen
  apply HilbertProofᵢ.gen
  change extended nativeTheory ⊢! _
  have hv : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb ((![#0,#1] : Fin 2 → Semiterm language Empty 2) i)))) = ![&0, &1] := by
    funext i
    cases i using Fin.cases with
    | zero =>
      change Rew.free (Rew.free (#(0 : Fin 2) : Semiterm language ℕ 2)) = &0
      rw [Rew.free_bvar_castSucc_zero, Rew.free_bvar_last_zero]
    | succ j => cases j using Fin.cases with
      | zero =>
        change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
        rw [Rew.free_bvar_last, Rew.free_fvar]
      | succ j => exact Fin.elim0 j
  have hf1 : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb (![.func subCode ![#0,#1], zeroTerm 2] i)))) =
      ![.func subCode ![&0,&1], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, hv]
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hf2 : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb (![.func subCode ![#1,#0], zeroTerm 2] i)))) =
      ![.func subCode ![&1,&0], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext k; cases k using Fin.cases with
      | zero => change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1; rw [Rew.free_bvar_last, Rew.free_fvar]
      | succ j => cases j using Fin.cases with
        | zero => change Rew.free (Rew.free (#(0 : Fin 2) : Semiterm language ℕ 2)) = &0; rw [Rew.free_bvar_castSucc_zero, Rew.free_bvar_last_zero]
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simpa [eqMatrix, diff1, diff2, zeroOpen, eqAt, Semiformulaᵢ.rewAux,
    Semiformulaᵢ.rew_rel, Rewriting.free, Rew.func, Function.comp_def, hv, hf1, hf2, a, b, c, x, y] using ho
/-- Native equality decision follows from the two explicit induction cases. -/
def equalityDecidable (hbase : nativeTheory ⊢! baseSentence) (hstep : nativeTheory ⊢! stepSentence) :
    nativeTheory ⊢! eqDecSentence :=
  DiophantineConsistency.IPRADifferenceEqualityZeroJoin.equalityDecidable (reverseFromInvariant hbase hstep)
end DiophantineConsistency.IPRADifferenceInvariant
