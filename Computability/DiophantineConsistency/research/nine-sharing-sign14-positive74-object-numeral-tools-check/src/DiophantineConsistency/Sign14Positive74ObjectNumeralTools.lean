import DiophantineConsistency.Sign14Positive74ObjectMulZeroNative
import DiophantineConsistency.IPRAZeroLeft

/-! SOURCE ONLY: native open zero-left and equality transitivity. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectNumeralTools
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory IPRANativeInduction IPRATheoryHilbertBridge
open IPRATheoryInstantiation IPRANativeAtomStability IPRAFunctionCongruenceOpen
open Sign14Positive74ObjectPredecessor Sign14Positive74ObjectMulZeroContext Sign14Positive74ObjectMulZeroNative
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def zeroLeftOpen (a : Term language ℕ) : extended nativeTheory ⊢!
    eqAt (.func addCode ![zero,a]) a := by
  have ha : nativeTheory ⊢! ∀⁰* IPRAZeroLeft.matrix := by
    apply Classical.choice
    simpa [allClosure_succ, Entailment.Provable] using IPRAZeroLeft.zero_left
  have hp := instantiateTheory (T := nativeTheory) IPRAZeroLeft.matrix ha ![a]
  have hv : (fun i : Fin 2 => (Rew.embSubsts ![a])
      (![.func addCode ![zeroTerm 1,#0], #0] i)) = ![.func addCode ![zero,a],a] := by
    funext i
    fin_cases i <;> simp [zeroTerm, zero, Rew.func, Function.comp_def, funext_iff]
  simpa [IPRAZeroLeft.matrix, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel,
    Function.comp_def, hv] using hp

def transOpen (a b c : Term language ℕ) : extended nativeTheory ⊢!
    (eqAt a b 🡒 eqAt b c 🡒 eqAt a c) := by
  have hctx := Classical.choice (contextNative _ (trans_context Δ (by simp [Δ]) a b c))
  have hp : extended nativeTheory ⊢! ⋀hctx.ctx 🡒 (eqAt a b 🡒 eqAt b c 🡒 eqAt a c) :=
    HilbertProofᵢ.ofLE (le_extended nativeTheory) hctx.prf
  have hc : extended nativeTheory ⊢! ⋀hctx.ctx :=
    Entailment.Conj₂_intro hctx.ctx (fun ψ hψ => HilbertProofᵢ.eaxm (Or.inr (hctx.subset ψ hψ)))
  exact hp ⨀ hc
end DiophantineConsistency.Sign14Positive74ObjectNumeralTools
#print axioms DiophantineConsistency.Sign14Positive74ObjectNumeralTools.zeroLeftOpen
#print axioms DiophantineConsistency.Sign14Positive74ObjectNumeralTools.transOpen
