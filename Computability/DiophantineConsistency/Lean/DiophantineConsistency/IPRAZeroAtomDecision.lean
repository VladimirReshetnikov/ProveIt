import DiophantineConsistency.IPRAOpenAtomDecision
/-! Every open NNF formula whose atoms compare terms with zero admits
GG-to-native transfer from an explicit native zero-decidability proof. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAZeroAtomDecision
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRANativeInduction
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRAOpenAtomDecision
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def zeroEq : Semisentenceᵢ language 1 := .rel .eq ![#0, zeroTerm 1]
def zeroDec : Semisentenceᵢ language 1 := zeroEq ⋎ ∼zeroEq
def zeroDecSentence : Sentenceᵢ language := ∀⁰ zeroDec
def zero : Term language ℕ := .func (.zero 0) Fin.elim0

def decideZero (hz : nativeTheory ⊢! zeroDecSentence) (t : Term language ℕ) :
    extended nativeTheory ⊢! (.rel .eq ![t,zero] : Propositionᵢ language) ⋎ ∼(.rel .eq ![t,zero]) := by
  have hdec := instantiateTheory (T := nativeTheory) zeroDec hz ![t]
  have hv : (fun i : Fin 2 => Rew.embSubsts ![t] (![#0, zeroTerm 1] i)) = ![t,zero] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp [zero, zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simpa [zeroDec, zeroEq, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hdec

theorem positiveAtom (hz : nativeTheory ⊢! zeroDecSentence) (t : Term language ℕ) :
    AtomDecisions (Semiformula.rel Language.ORing.Rel.eq ![t,zero]) := by
  rw [AtomDecisions.eq_1]
  exact ⟨decideZero hz t⟩

theorem negativeAtom (hz : nativeTheory ⊢! zeroDecSentence) (t : Term language ℕ) :
    AtomDecisions (Semiformula.nrel Language.ORing.Rel.eq ![t,zero]) := by
  rw [AtomDecisions.eq_2]
  exact ⟨decideZero hz t⟩
/-- Open NNF formulas all of whose atoms compare a term with zero. -/
inductive ZeroOpen : Proposition language → Prop
  | positive (t : Term language ℕ) : ZeroOpen (.rel .eq ![t,zero])
  | negative (t : Term language ℕ) : ZeroOpen (.nrel .eq ![t,zero])
  | verum : ZeroOpen ⊤
  | falsum : ZeroOpen ⊥
  | conj {φ ψ} : ZeroOpen φ → ZeroOpen ψ → ZeroOpen (.and φ ψ)
  | disj {φ ψ} : ZeroOpen φ → ZeroOpen ψ → ZeroOpen (.or φ ψ)

theorem zeroOpenAtoms (hz : nativeTheory ⊢! zeroDecSentence) {φ : Proposition language}
    (h : ZeroOpen φ) : AtomDecisions φ := by
  induction h with
  | positive t => exact positiveAtom hz t
  | negative t => exact negativeAtom hz t
  | verum =>
    change AtomDecisions Semiformula.verum
    rw [AtomDecisions.eq_3]
    trivial
  | falsum =>
    change AtomDecisions Semiformula.falsum
    rw [AtomDecisions.eq_4]
    trivial
  | @conj φ ψ _ _ ihφ ihψ =>
    rw [AtomDecisions.eq_5]
    exact ⟨ihφ, ihψ⟩
  | @disj φ ψ _ _ ihφ ihψ =>
    rw [AtomDecisions.eq_6]
    exact ⟨ihφ, ihψ⟩

def zeroOpenBackward (hz : nativeTheory ⊢! zeroDecSentence) (φ : Proposition language)
    (h : ZeroOpen φ) : extended nativeTheory ⊢! φᴺ 🡒 native φ :=
  backward φ (zeroOpenAtoms hz h)

end DiophantineConsistency.IPRAZeroAtomDecision
