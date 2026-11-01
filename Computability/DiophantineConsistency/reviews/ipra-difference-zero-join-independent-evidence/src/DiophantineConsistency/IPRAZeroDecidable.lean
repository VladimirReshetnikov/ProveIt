import DiophantineConsistency.IPRANativeAxiomImage
import DiophantineConsistency.IPRAAllSpecialize
/-! Zero decidability from the explicit remaining addition-step nonzero
premise. This file does not prove that premise or full equality decidability. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAZeroDecidable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory IPRAQuantifierFree IPRANativeInduction IPRANativeTheory IPRANativeAxiomImage

local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def zeroEq : Semisentenceᵢ language 1 := .rel .eq ![#0, zeroTerm 1]
def zeroDec : Semisentenceᵢ language 1 := zeroEq ⋎ ∼zeroEq
def zeroDecSentence : Sentenceᵢ language := ∀⁰ zeroDec
def stepNonzero : Sentenceᵢ language := ∀⁰ (∼atStep zeroEq)

theorem zeroDec_open : OpenI zeroDec := by
  simp [zeroDec, zeroEq, OpenI]

theorem zeroDec_induction : nativeTheory ⊢ inductionAxiom zeroDec :=
  native_axiom (NativeAxiom.induction ⟨0, zeroDec, zeroDec_open, rfl⟩)

theorem base : nativeTheory ⊢ atZero zeroDec := by
  have hr : nativeTheory ⊢ eqReflI := native_axiom (NativeAxiom.equality EqualityAxiomI.refl)
  have hs : nativeTheory ⊢ atZero zeroEq := by
    have hs' := IPRAAllSpecialize.allClosure_specialize (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language)) 1
      (Rewriting.emb (Semiformulaᵢ.rel Language.ORing.Rel.eq ![#0,#0] : Semisentenceᵢ language 1))
      (fun _ => (.func (PRAFiniteFunctionCodes.Code.zero 0) Fin.elim0 : SyntacticTerm language))
    have hs'' := Classical.choice hs'
    have h := Entailment.mdp! (show nativeTheory ⊢ eqReflI 🡒 atZero zeroEq by
      apply Nonempty.intro
      apply Theoryᵢ.ofHilbert
      convert hs'' using 1
      simp [eqReflI, atZero, zeroEq, zeroTerm, Rewriting.subst, Semiformulaᵢ.rew_rel]
      funext i
      cases i using Fin.cases with
      | zero =>
        simp [Rew.func, Function.comp_def]
        funext i
        exact Fin.elim0 i
      | succ j =>
        cases j using Fin.cases with
        | zero =>
          simp [Rew.func, Function.comp_def]
          funext i
          exact Fin.elim0 i
        | succ j => exact Fin.elim0 j) hr
    exact h
  have ho : nativeTheory ⊢ atZero zeroEq 🡒 atZero zeroDec := by
    apply Nonempty.intro
    apply Theoryᵢ.ofHilbert
    simpa [atZero, zeroDec] using (Entailment.or₁ (𝓢 := (𝗜𝗻𝘁¹ : Hilbertᵢ language))
      (φ := Rewriting.emb (atZero zeroEq)) (ψ := ∼Rewriting.emb (atZero zeroEq)))
  exact Entailment.mdp! ho hs

theorem all_step_of_nonzero {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}
    (p q : Semipropositionᵢ L 1) :
    Λ ⊢ (∀⁰ ∼q) 🡒 ∀⁰ (p 🡒 (q ⋎ ∼q)) := by
  have hp : Λ ⊢! (∼Rewriting.free q) 🡒
      (Rewriting.free p 🡒 (Rewriting.free q ⋎ ∼Rewriting.free q)) :=
    Entailment.C_trans Entailment.or₂ Entailment.implyK
  have hg : Λ ⊢! Rewriting.free ((∼q) 🡒 (p 🡒 (q ⋎ ∼q))) := by
    simpa using hp
  exact ⟨HilbertProofᵢ.allImplyAllOfAllImply _ _ ⨀ HilbertProofᵢ.gen hg⟩

theorem step_of_nonzero (hstep : nativeTheory ⊢ stepNonzero) :
    nativeTheory ⊢ ∀⁰ (zeroDec 🡒 atStep zeroDec) := by
  have hl := all_step_of_nonzero (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language))
    (Rewriting.emb zeroDec) (Rewriting.emb (atStep zeroEq))
  have htheory : nativeTheory ⊢ stepNonzero 🡒 ∀⁰ (zeroDec 🡒 atStep zeroDec) := by
    apply Nonempty.intro
    apply Theoryᵢ.ofHilbert
    have hh := Classical.choice hl
    convert hh using 1
    simp [stepNonzero, zeroDec, atStep]
  exact Entailment.mdp! htheory hstep

theorem zero_decidable_of_step (hstep : nativeTheory ⊢ stepNonzero) :
    nativeTheory ⊢ zeroDecSentence := by
  have h := Entailment.mdp! zeroDec_induction base
  exact Entailment.mdp! h (step_of_nonzero hstep)
end DiophantineConsistency.IPRAZeroDecidable
