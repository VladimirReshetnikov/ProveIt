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
      have t : extended nativeTheory ⊢!
          ((guard 🡒 eqAt ((mix s v w) i) (w i)) 🡒
            ((guard 🡒 ((Rew.embSubsts v ▹ φ) 🡒 (Rew.embSubsts (mix s v w) ▹ φ))) 🡒
              ((eqAt ((mix s v w) i) (w i) 🡒
                ((Rew.embSubsts (mix s v w) ▹ φ) 🡒
                  (Rew.embSubsts (Function.update (mix s v w) i (w i)) ▹ φ))) 🡒
                (guard 🡒 ((Rew.embSubsts v ▹ φ) 🡒
                  (Rew.embSubsts (Function.update (mix s v w) i (w i)) ▹ φ)))))) := by
        apply Classical.choice
        change extended nativeTheory ⊢ _
        int_prover
      apply Nonempty.intro
      simpa only [mix_insert] using (t ⨀ he ⨀ Classical.choice ih ⨀ step)
  apply Classical.choice
  simpa only [huniv] using hm Finset.univ
end DiophantineConsistency.Sign14Positive74ObjectMultiSubst
#print axioms DiophantineConsistency.Sign14Positive74ObjectMultiSubst.guardedAllSubstitution
