import DiophantineConsistency.Sign14Positive74ObjectCoordinateNative

/-! SOURCE-ONLY: iterate actual native substitution under a common guard. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectMultiSubst
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRAFiniteFunctionCodes IPRANativeTheory IPRANativeAtomStability
open IPRATheoryHilbertBridge IPRAFunctionCongruenceOpen Sign14Positive74ObjectCoordinateNative
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def guardedChain (g e a b c : Propositionᵢ language)
    (he : extended nativeTheory ⊢! (g 🡒 e))
    (hab : extended nativeTheory ⊢! (g 🡒 (a 🡒 b)))
    (step : extended nativeTheory ⊢! (e 🡒 (b 🡒 c))) :
    extended nativeTheory ⊢! (g 🡒 (a 🡒 c)) := by
  apply Entailment.FiniteContext.deduct'
  apply Entailment.FiniteContext.deduct
  let Γ : List (Propositionᵢ language) := [a,g]
  have ha : Γ ⊢[extended nativeTheory]! a := Entailment.FiniteContext.byAxm₀
  have hg : Γ ⊢[extended nativeTheory]! g := Entailment.FiniteContext.byAxm₁
  have he' : Γ ⊢[extended nativeTheory]! e := (Entailment.FiniteContext.of he) ⨀ hg
  have hb : Γ ⊢[extended nativeTheory]! b := (Entailment.FiniteContext.of hab) ⨀ hg ⨀ ha
  exact (Entailment.FiniteContext.of step) ⨀ he' ⨀ hb

def guardedAllSubstitution {n : ℕ} (φ : Semisentenceᵢ language (n+1))
    (v w : Fin (n+1) → Term language ℕ) (guard : Propositionᵢ language)
    (h : ∀ i, extended nativeTheory ⊢! (guard 🡒 eqAt (v i) (w i))) :
    extended nativeTheory ⊢! (guard 🡒 ((Rew.embSubsts v ▹ φ) 🡒 (Rew.embSubsts w ▹ φ))) := by
  have hempty : mix ∅ v w = v := by funext i; simp [mix]
  have huniv : mix Finset.univ v w = w := by funext i; simp [mix]
  have hm : ∀ s : Finset (Fin (n+1)), extended nativeTheory ⊢
      (guard 🡒 ((Rew.embSubsts v ▹ φ) 🡒 (Rew.embSubsts (mix s v w) ▹ φ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [hempty]
      apply Nonempty.intro
      apply Classical.choice
      change extended nativeTheory ⊢ _
      int_prover
    | @insert i s hi ih =>
      have he : extended nativeTheory ⊢! (guard 🡒 eqAt ((mix s v w) i) (w i)) := by
        simpa [mix, hi] using h i
      have step := updateOpen φ (mix s v w) i (w i)
      have t := guardedChain guard (eqAt ((mix s v w) i) (w i))
        (Rew.embSubsts v ▹ φ) (Rew.embSubsts (mix s v w) ▹ φ)
        (Rew.embSubsts (Function.update (mix s v w) i (w i)) ▹ φ)
        he (Classical.choice ih) step
      have hup : IPRAFunctionCongruenceOpen.update i (w i) (mix s v w) =
          Function.update (mix s v w) i (w i) := by
        funext j
        by_cases hji : j = i <;> simp [IPRAFunctionCongruenceOpen.update, hji]
      apply Nonempty.intro
      simpa only [mix_insert, hup] using t
  apply Classical.choice
  change extended nativeTheory ⊢ _
  simpa only [huniv] using hm Finset.univ
end DiophantineConsistency.Sign14Positive74ObjectMultiSubst
#print axioms DiophantineConsistency.Sign14Positive74ObjectMultiSubst.guardedAllSubstitution
