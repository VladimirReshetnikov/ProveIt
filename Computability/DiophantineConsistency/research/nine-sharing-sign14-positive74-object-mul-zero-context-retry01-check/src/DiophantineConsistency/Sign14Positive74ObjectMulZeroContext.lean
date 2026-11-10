import DiophantineConsistency.Sign14Positive74ObjectShiftPartial
import DiophantineConsistency.IPRAAddOneDirect

/-! SOURCE ONLY: derive x*0=0 from a finite displayed axiom context. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectMulZeroContext
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRADefiningInstances IPRAFunctionCongruenceOpen IPRAAddOneDirect
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def mulStep : Code 3 := .comp addCode (.cons (.proj 1) (.cons (.proj 2) (.nil 3)))
def mulBaseAx : Propositionᵢ language := Rewriting.emb (recursionBaseEquationI (.zero 1) mulStep)
def zeroAx : Propositionᵢ language := Rewriting.emb (zeroEquationI 1)
def Δ : List (Propositionᵢ language) := [
  compAx mulCore swapArgs, projAx (0 : Fin 2), projAx (1 : Fin 2), mulBaseAx, zeroAx,
  IPRAEqualityTransGG.ax, reflAx, funAx mulCore (0 : Fin 2), funAx mulCore (1 : Fin 2)]
def mz : SyntacticTerm language := .func (.zero 0) Fin.elim0
def mcore (a b : SyntacticTerm language) : SyntacticTerm language := .func mulCore ![a,b]
def mult (a b : SyntacticTerm language) : SyntacticTerm language := .func mulCode ![a,b]

theorem trans {a b c : SyntacticTerm language} (h : Δ ⊢[𝗜𝗻𝘁¹] equal a b)
    (j : Δ ⊢[𝗜𝗻𝘁¹] equal b c) : Δ ⊢[𝗜𝗻𝘁¹] equal a c :=
  Entailment.mdp! (Entailment.mdp! (trans_context Δ (by simp [Δ]) a b c) h) j

theorem core_congr {a b c d : SyntacticTerm language}
    (h : Δ ⊢[𝗜𝗻𝘁¹] equal a b) (j : Δ ⊢[𝗜𝗻𝘁¹] equal c d) :
    Δ ⊢[𝗜𝗻𝘁¹] equal (mcore a c) (mcore b d) := by
  have hx : ∀ i : Fin 2, funAx mulCore i ∈ Δ := by
    intro i; fin_cases i <;> simp [Δ]
  have hr : ∀ i : Fin 2, Δ ⊢[𝗜𝗻𝘁¹] equal (![a,c] i) (![b,d] i) := by
    intro i; fin_cases i <;> assumption
  exact function_open_in_context mulCore Δ (by simp [Δ]) (by simp [Δ]) hx _ _ hr

theorem proj0 (a b : SyntacticTerm language) :
    Δ ⊢[𝗜𝗻𝘁¹] equal (.func (.proj 0) ![a,b]) a := by
  have h : Δ ⊢[𝗜𝗻𝘁¹] projAx (0 : Fin 2) := ⟨FiniteContext.byAxm (by simp [Δ])⟩
  simpa [equal, IPRANativeEquationSpecialize.equal] using projection_instance (0 : Fin 2) ![a,b] Δ h

theorem proj1 (a b : SyntacticTerm language) :
    Δ ⊢[𝗜𝗻𝘁¹] equal (.func (.proj 1) ![a,b]) b := by
  have h : Δ ⊢[𝗜𝗻𝘁¹] projAx (1 : Fin 2) := ⟨FiniteContext.byAxm (by simp [Δ])⟩
  simpa [equal, IPRANativeEquationSpecialize.equal] using projection_instance (1 : Fin 2) ![a,b] Δ h

theorem swap (a b : SyntacticTerm language) : Δ ⊢[𝗜𝗻𝘁¹] equal (mult a b) (mcore b a) := by
  have h : Δ ⊢[𝗜𝗻𝘁¹] compAx mulCore swapArgs := ⟨FiniteContext.byAxm (by simp [Δ])⟩
  have hs := composition_instance mulCore swapArgs ![a,b] Δ h
  have hc := core_congr (proj1 a b) (proj0 a b)
  apply trans ?_ hc
  convert hs using 1
  simp [mult, mcore, mulCode, swapArgs, getCode, equal, IPRANativeEquationSpecialize.equal]
  funext i; fin_cases i <;> rfl

theorem base (a : SyntacticTerm language) :
    Δ ⊢[𝗜𝗻𝘁¹] equal (mcore mz a) (.func (.zero 1) ![a]) := by
  have h : Δ ⊢[𝗜𝗻𝘁¹] mulBaseAx := ⟨FiniteContext.byAxm (by simp [Δ])⟩
  have hs := recursion_base_instance (.zero 1) mulStep ![a] Δ h
  convert hs using 1
  simp [mcore, mz, mulCore, mulStep, equal, IPRANativeEquationSpecialize.equal]
  funext i; fin_cases i <;> rfl

theorem unary_zero (a : SyntacticTerm language) : Δ ⊢[𝗜𝗻𝘁¹] equal (.func (.zero 1) ![a]) mz := by
  have h : Δ ⊢[𝗜𝗻𝘁¹] zeroAx := ⟨FiniteContext.byAxm (by simp [Δ])⟩
  have hs := IPRANativeEquationSpecialize.specialize_equalClosureI (applyCode (.zero 1) (vars 1))
    (applyCode (.zero 0) Fin.elim0) ![a] Δ (by simpa [zeroAx, zeroEquationI] using h)
  convert hs using 1
  simp [mz, applyCode, vars, equal, IPRANativeEquationSpecialize.equal, Rew.func, Function.comp_def]
  constructor
  · funext i
    fin_cases i <;> rfl
  · funext i
    exact Fin.elim0 i

theorem mul_zero (a : SyntacticTerm language) : Δ ⊢[𝗜𝗻𝘁¹] equal (mult a mz) mz :=
  trans (swap a mz) (trans (base a) (unary_zero a))
end DiophantineConsistency.Sign14Positive74ObjectMulZeroContext
#print axioms DiophantineConsistency.Sign14Positive74ObjectMulZeroContext.mul_zero
