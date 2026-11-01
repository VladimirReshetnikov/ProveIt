import DiophantineConsistency.PRABitConvention
import DiophantineConsistency.IPRASelectorSearchBinding
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRABitConvention
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRABitConvention PRAIsZero PRAAddOne
open IPRANativeFormula IPRANativeTheory IPRASelectorSearchBinding IPRABoundedSelector
open IPRAOpenAtomDecision IPRATheoryHilbertBridge IPRATheoryInstantiation
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def transferOpen {n : ℕ} (φ : Semisentence language n) (hopen : φ.Open)
    (hproof : PRA ⊢ ∀⁰* φ) (v : Fin n → Term language ℕ) :
    extended nativeTheory ⊢! native (Rew.embSubsts v ▹ φ) := by
  have ht := IPRAFullGGTransfer.from_classical hproof
  have hgg : nativeTheory ⊢! ∀⁰* φᴺ := by
    have h := Classical.choice ht
    simpa only [IPRAQuantifierFree.gg_allClosure] using h
  have hs := instantiateTheory (T := nativeTheory) φᴺ hgg v
  have ho : (Rew.embSubsts v ▹ φ).Open := by simpa using hopen
  have hr := backward (Rew.embSubsts v ▹ φ) (openAtoms _ ho)
  apply hr ⨀ ?_
  simpa only [Semiformula.rew_doubleNegation] using hs

def zero : Term language ℕ := .func (.zero 0) Fin.elim0
def one : Term language ℕ := .func oneCode Fin.elim0
def iszero (t : Term language ℕ) : Term language ℕ := .func isZeroCode (fun _ => t)
def eq (t u : Term language ℕ) : Propositionᵢ language := .rel .eq ![t,u]

def convention (t : Term language ℕ) : extended nativeTheory ⊢!
   (eq t zero ⋎ eq t one) 🡒 (eq (iszero t) zero 🡘 eq t one) := by
  have hs := transferOpen matrix matrix_open PRA_proves_sentence ![t]
  have htz : Rew.embSubsts ![t] z = zero := by
    simp [z, zero, applyCode, Rew.func, Function.comp_def]
    funext j; exact Fin.elim0 j
  have hto : Rew.embSubsts ![t] o = one := by
    simp [o, one, applyCode, Rew.func, Function.comp_def]
    funext j; exact Fin.elim0 j
  have hti : Rew.embSubsts ![t] iz = iszero t := by
    simp [iz, iszero, applyCode, Rew.func, Function.comp_def]
  have hl : extended nativeTheory ⊢! native (Rew.embSubsts ![t] ▹ matrix) 🡒
     ((eq t zero ⋎ eq t one) 🡒 (eq (iszero t) zero 🡘 eq t one)) := by
    simp [matrix, Semiformula.neg, IPRANativeFormula.native, eq, htz, hto, hti]
    apply Classical.choice
    change extended nativeTheory ⊢ _
    int_prover
  exact hl ⨀ hs
end DiophantineConsistency.IPRABitConvention
