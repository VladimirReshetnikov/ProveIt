import DiophantineConsistency.IPRABoundedLogic
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRABoundedInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeFormula IPRANativeFormulaRew IPRACharacteristicTransfer IPRABoundedShape IPRABoundedChild
open IPRAOpenAtomDecision IPRABoundedSelector IPRABoundedErasureLogic IPRAExistentialComparison
open IPRANativeOpenDecision IPRANativeAtomStability IPRABoundedLogic
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def boundedAll {n : ℕ} (t : TermN n) (φ : Semisentence language (n+1)) : Semisentence language n :=
  ∀⁰[(Semiformula.rel Language.ORing.Rel.lt ![#0, Rew.bShift t])] φ

def boundedAllBackward {Γ : Polarity} {n : ℕ} (t : TermN n) (φ : Semisentence language (n+1))
    (hφ : Hierarchy Γ 0 φ) (e : Fin n → Term language ℕ)
    (hback : ∀ u : Fin (n+1) → Term language ℕ,
      extended nativeTheory ⊢! (Rew.embSubsts u ▹ φ)ᴺ 🡒 native (Rew.embSubsts u ▹ φ)) :
    extended nativeTheory ⊢! (Rew.embSubsts e ▹ boundedAll t φ)ᴺ 🡒 native (Rew.embSubsts e ▹ boundedAll t φ) := by
  let r : Semisentence language (n+1) := .nrel .lt ![#0, Rew.bShift t]
  let body : Semiproposition language 1 := (Rew.embSubsts e).q ▹ (r ⋎ φ)
  let u : Fin (n+1) → Term language ℕ := Fin.cases (&0) (fun i => Rew.shift (e i))
  have hrew : (Rew.free (L := language) (n := 0)).comp (Rew.embSubsts e).q = Rew.embSubsts u := by
    ext i
    · cases i using Fin.cases <;> simp [Rew.comp_app, Rew.q_embSubsts, u]
    · exact Empty.elim i
  have hgopen : (Rew.embSubsts u ▹ r).Open := by simp [r, Semiformula.Open]
  have hg := backward (Rew.embSubsts u ▹ r) (openAtoms _ hgopen)
  have hc := hback u
  have hgd := DiophantineConsistency.IPRANativeOpenDecidable.openDecidable (Rew.embSubsts u ▹ r) hgopen
  have hcd := decideBoundedFromBackward φ hφ u hc
  have hor := orBackward (Rew.embSubsts u ▹ r) (Rew.embSubsts u ▹ φ) hg hc hgd hcd
  have hfree : extended nativeTheory ⊢! Rewriting.free (bodyᴺ) 🡒 Rewriting.free (native body) := by
    simpa [body, native_rew, Semiformula.rew_doubleNegation, Rewriting.free,
      ← TransitiveRewriting.comp_app, hrew, IPRANativeFormula.native] using hor
  have hcomp := eraseAll hfree
  change extended nativeTheory ⊢! (∀⁰ body)ᴺ 🡒 native (∀⁰ body)
  simpa only [IPRANativeFormula.native, Semiformula.doubleNegation_all] using hcomp

theorem backwardAux {Γ : Polarity} {s n : ℕ} {φ : Semisentence language n}
    (h : Hierarchy Γ s φ) (hs : s = 0) :
    ∀ e : Fin n → Term language ℕ,
      extended nativeTheory ⊢ (Rew.embSubsts e ▹ φ)ᴺ 🡒 native (Rew.embSubsts e ▹ φ) := by
  induction h with
  | verum => intro e; exact ⟨Entailment.C_id⟩
  | falsum => intro e; exact ⟨Entailment.C_id⟩
  | rel _ _ r v =>
      intro e
      apply Nonempty.intro
      apply backward
      apply openAtoms
      simp [Semiformula.Open]
  | nrel _ _ r v =>
      intro e
      apply Nonempty.intro
      apply backward
      apply openAtoms
      simp [Semiformula.Open]
  | and hφ hψ ihφ ihψ =>
      intro e
      have ha := Classical.choice (ihφ hs e)
      have hb := Classical.choice (ihψ hs e)
      apply Nonempty.intro
      simpa [IPRANativeFormula.native] using Entailment.CK_of_C_of_C (Entailment.C_trans Entailment.and₁ ha)
        (Entailment.C_trans Entailment.and₂ hb)
  | or hφ hψ ihφ ihψ =>
      intro e
      have ha := Classical.choice (ihφ hs e)
      have hb := Classical.choice (ihψ hs e)
      have had := decideBoundedFromBackward _ (by simpa [hs] using hφ) e ha
      have hbd := decideBoundedFromBackward _ (by simpa [hs] using hψ) e hb
      apply Nonempty.intro
      simpa using orBackward _ _ ha hb had hbd
  | ball ht hφ ih =>
      obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
      intro e
      have hback := fun u => Classical.choice (ih hs u)
      apply Nonempty.intro
      change extended nativeTheory ⊢! (Rew.embSubsts e ▹ boundedAll t _)ᴺ 🡒 native (Rew.embSubsts e ▹ boundedAll t _)
      exact boundedAllBackward t _ (by simpa [hs] using hφ) e hback
  | bexs ht hφ ih =>
      obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
      intro e
      have hback := fun u => Classical.choice (ih hs u)
      apply Nonempty.intro
      change extended nativeTheory ⊢! (Rew.embSubsts e ▹ bounded t _)ᴺ 🡒 native (Rew.embSubsts e ▹ bounded t _)
      exact boundedExistsBackward t _ (by simpa [hs] using hφ) e hback
  | exs => omega
  | all => omega
  | sigma => omega
  | pi => omega
  | dummy_sigma => omega
  | dummy_pi => omega
/-- Uniform open family of native GG comparisons for any bounded hierarchy polarity. -/
def backward {Γ : Polarity} {n : ℕ} (φ : Semisentence language n)
    (hφ : Hierarchy Γ 0 φ) (e : Fin n → Term language ℕ) :
    extended nativeTheory ⊢! (Rew.embSubsts e ▹ φ)ᴺ 🡒 native (Rew.embSubsts e ▹ φ) :=
  Classical.choice (backwardAux hφ rfl e)
end DiophantineConsistency.IPRABoundedInduction
