import DiophantineConsistency.IPRAZeroDecidable
import DiophantineConsistency.IPRAAddOneTransfer
set_option autoImplicit false
namespace DiophantineConsistency.IPRAZeroStepNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRALanguage PRATheory IPRANativeTheory IPRANativeInduction IPRAZeroDecidable

local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def eqI {n : ℕ} (x y : Semiterm language ℕ n) : Semiformulaᵢ language ℕ n :=
  .rel .eq ![x,y]
def succTerm : TermN 1 := applyCode .succ (fun _ => #0)
def addOneNN : Sentenceᵢ language := ∀⁰ (∼∼(.rel .eq ![stepTerm 0, succTerm]))
def addAx : Propositionᵢ language := Rewriting.emb addOneNN
def succAx : Propositionᵢ language := Rewriting.emb succNonzeroI
def leibAx : Propositionᵢ language := Rewriting.emb (eqSubstitutionI zeroEq)
def stepFree : SyntacticTerm language := .func addCode ![&0, .func oneCode Fin.elim0]
def succFree : SyntacticTerm language := .func .succ (fun _ => &0)
def zeroFree : SyntacticTerm language := .func (PRAFiniteFunctionCodes.Code.zero 0) Fin.elim0

theorem step_open : [addAx,succAx,leibAx] ⊢[𝗜𝗻𝘁¹] ∼eqI stepFree zeroFree := by
  apply FiniteContext.deduct!
  let Γ : List (Propositionᵢ language) := [eqI stepFree zeroFree,addAx,succAx,leibAx]
  have ha : Γ ⊢[𝗜𝗻𝘁¹]! addAx := FiniteContext.byAxm₁
  have hs : Γ ⊢[𝗜𝗻𝘁¹]! succAx := FiniteContext.byAxm₂
  have hl : Γ ⊢[𝗜𝗻𝘁¹]! leibAx := FiniteContext.byAxm (by simp [Γ])
  have hq : Γ ⊢[𝗜𝗻𝘁¹]! eqI stepFree zeroFree := FiniteContext.byAxm₀
  have hn := HilbertProofᵢ.specializeOverContext ha (&0 : SyntacticTerm language)
  have hs' := HilbertProofᵢ.specializeOverContext hs (&0 : SyntacticTerm language)
  have hl' := IPRAAllSpecialize.specialize_native_leibniz zeroEq ![stepFree,succFree] Γ ⟨hl⟩
  have hnn : Γ ⊢[𝗜𝗻𝘁¹]! ∼∼eqI stepFree succFree := by
    convert hn using 1
    simp [Semiformulaᵢ.rewAux, stepTerm, succTerm, stepFree, succFree, eqI,
      Semiformulaᵢ.rew_rel, Rewriting.subst, Function.comp_def]
    congr 3
    funext i
    cases i using Fin.cases with
    | zero =>
      simp [applyCode, Rew.func, Function.comp_def]
      funext j
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        cases j using Fin.cases with
        | zero =>
          simp [Rew.func, Function.comp_def]
          funext z
          exact Fin.elim0 z
        | succ j => exact Fin.elim0 j
    | succ j =>
      cases j using Fin.cases with
      | zero => simp [applyCode, Rew.func, Function.comp_def]
      | succ j => exact Fin.elim0 j
  have hns : Γ ⊢[𝗜𝗻𝘁¹]! ∼eqI succFree zeroFree := by
    convert hs' using 1
    simp [Semiformulaᵢ.rewAux, succFree, zeroFree, applyCode, eqI,
      Semiformulaᵢ.rew_rel, Rewriting.subst, Function.comp_def]
    congr 2
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]
    | succ j =>
      cases j using Fin.cases with
      | zero =>
        simp [Rew.func, Function.comp_def]
        funext z
        exact Fin.elim0 z
      | succ j => exact Fin.elim0 j
  have hp : Γ ⊢[𝗜𝗻𝘁¹]! eqI stepFree succFree 🡒 eqI stepFree zeroFree 🡒 eqI succFree zeroFree := by
    have hh := Classical.choice hl'
    convert hh using 1
    simp [IPRAAllSpecialize.leibnizBody, eqLeft, eqRight, zeroEq, zeroTerm,
      stepFree, succFree, zeroFree, eqI, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_,?_,?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => simp
    | succ j =>
      cases j using Fin.cases with
      | zero => simp <;> funext z <;> exact Fin.elim0 z
      | succ j => exact Fin.elim0 j
  have hnotp : Γ ⊢[𝗜𝗻𝘁¹]! ∼eqI stepFree succFree := by
    apply FiniteContext.deduct
    let Δ : List (Propositionᵢ language) := eqI stepFree succFree :: Γ
    have hP : Δ ⊢[𝗜𝗻𝘁¹]! eqI stepFree succFree := FiniteContext.byAxm₀
    have hQ : Δ ⊢[𝗜𝗻𝘁¹]! eqI stepFree zeroFree := FiniteContext.weakening (by simp [Δ]) hq
    have hN : Δ ⊢[𝗜𝗻𝘁¹]! ∼eqI succFree zeroFree := FiniteContext.weakening (by simp [Δ]) hns
    have hC : Δ ⊢[𝗜𝗻𝘁¹]! eqI stepFree succFree 🡒 eqI stepFree zeroFree 🡒 eqI succFree zeroFree :=
      FiniteContext.weakening (by simp [Δ]) hp
    exact hN ⨀ ((hC ⨀ hP) ⨀ hQ)
  exact ⟨hnn ⨀ hnotp⟩
def stepBody : Semiformulaᵢ language ℕ 1 :=
  ∼eqI (.func addCode ![#0, .func oneCode Fin.elim0]) (.func (.zero 0) Fin.elim0)

theorem step_closed_context : [addAx,succAx,leibAx] ⊢[𝗜𝗻𝘁¹] ∀⁰ stepBody := by
  let Γ : List (Propositionᵢ language) := [addAx,succAx,leibAx]
  have hΓ : Γ⁺ = Γ := by simp [Γ, addAx, succAx, leibAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  have ho := Classical.choice step_open
  convert ho using 1
  simp [stepBody, eqI, stepFree, zeroFree, Semiformulaᵢ.rew_rel, Rewriting.free]
  congr 2
  funext i
  cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext z; exact Fin.elim0 z
      | succ j => exact Fin.elim0 j
  | succ j => cases j using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext z; exact Fin.elim0 z
    | succ j => exact Fin.elim0 j
theorem step_nonzero_of_addNN (hadd : nativeTheory ⊢ addOneNN) : nativeTheory ⊢ stepNonzero := by
  let Γ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have ha : Γ *⊢[𝗜𝗻𝘁¹] addAx := hadd
  have hs : Γ *⊢[𝗜𝗻𝘁¹] succAx :=
    IPRANativeAxiomImage.native_axiom (NativeAxiom.basic BasicAxiomI.succNonzero)
  have hl : Γ *⊢[𝗜𝗻𝘁¹] leibAx :=
    IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution zeroEq))
  have hc : Γ *⊢[𝗜𝗻𝘁¹] ⋀[addAx,succAx,leibAx] := by
    apply Conj₂!_iff_forall_provable.mpr
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ha
    · exact hs
    · exact hl
  have hi : Γ *⊢[𝗜𝗻𝘁¹] ∀⁰ stepBody :=
    ⟨Context.mdp (Context.of (FiniteContext.toDef (Classical.choice step_closed_context)))
      (Classical.choice hc)⟩
  change Γ *⊢[𝗜𝗻𝘁¹] (Rewriting.emb stepNonzero : Propositionᵢ language)
  convert hi using 1
  simp [stepNonzero, atStep, zeroEq, zeroTerm, stepTerm, stepBody, eqI,
    Semiformulaᵢ.rew_rel]
  congr 2
  funext i
  cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext z; exact Fin.elim0 z
      | succ j => exact Fin.elim0 j
  | succ j => cases j using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext z; exact Fin.elim0 z
    | succ j => exact Fin.elim0 j
theorem zero_decidable_of_addNN (hadd : nativeTheory ⊢ addOneNN) :
    nativeTheory ⊢ zeroDecSentence :=
  zero_decidable_of_step (step_nonzero_of_addNN hadd)
theorem zero_decidable : nativeTheory ⊢ zeroDecSentence := by
  apply zero_decidable_of_addNN
  exact IPRAAddOneTransfer.transfer
end DiophantineConsistency.IPRAZeroStepNative
