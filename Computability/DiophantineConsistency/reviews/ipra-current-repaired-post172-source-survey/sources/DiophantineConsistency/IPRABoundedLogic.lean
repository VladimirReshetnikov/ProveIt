import DiophantineConsistency.IPRABoundedShape
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRABoundedLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRANativeFormula IPRANativeFormulaRew IPRACharacteristicTransfer IPRABoundedShape IPRABoundedChild
open IPRAOpenAtomDecision IPRABoundedSelector IPRABoundedErasureLogic IPRAExistentialComparison
open IPRANativeOpenDecision IPRANativeAtomStability
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def orBackward (a b : Proposition language)
    (ha : extended nativeTheory ⊢! aᴺ 🡒 native a)
    (hb : extended nativeTheory ⊢! bᴺ 🡒 native b)
    (had : extended nativeTheory ⊢! native a ⋎ ∼native a)
    (hbd : extended nativeTheory ⊢! native b ⋎ ∼native b) :
    extended nativeTheory ⊢! (a ⋎ b)ᴺ 🡒 native (a ⋎ b) := by
  have hdec := decOr _ _ ⨀ had ⨀ hbd
  have hstable := stableOfDec _ hdec
  have hleft : extended nativeTheory ⊢! ∼(native a ⋎ native b) 🡒 ∼aᴺ :=
    Entailment.C_trans (Entailment.contra Entailment.or₁) (Entailment.contra ha)
  have hright : extended nativeTheory ⊢! ∼(native a ⋎ native b) 🡒 ∼bᴺ :=
    Entailment.C_trans (Entailment.contra Entailment.or₂) (Entailment.contra hb)
  simpa [IPRANativeFormula.native] using
    (Entailment.C_trans (Entailment.contra (Entailment.CK_of_C_of_C hleft hright)) hstable)

def stableAnyBoundedExists {Γ : Polarity} {n : ℕ} (t : TermN n) (φ : Semisentence language (n+1))
    (hφ : Hierarchy Γ 0 φ) (e : Fin n → Term language ℕ)
    (hback : ∀ u : Fin (n+1) → Term language ℕ,
      extended nativeTheory ⊢! (Rew.embSubsts u ▹ φ)ᴺ 🡒 native (Rew.embSubsts u ▹ φ)) :
    extended nativeTheory ⊢! ∼∼native (Rew.embSubsts e ▹ bounded t φ) 🡒 native (Rew.embSubsts e ▹ bounded t φ) := by
  let h := boundedCharacteristicAny φ hφ
  let c := Classical.choose h
  have hc := Classical.choose_spec h
  simpa only [shape] using stableFromClassical c φ hc.1 hc.2 (Fin.cases (Rew.embSubsts e t) e) hback

def boundedExistsBackward {Γ : Polarity} {n : ℕ} (t : TermN n) (φ : Semisentence language (n+1))
    (hφ : Hierarchy Γ 0 φ) (e : Fin n → Term language ℕ)
    (hback : ∀ u : Fin (n+1) → Term language ℕ,
      extended nativeTheory ⊢! (Rew.embSubsts u ▹ φ)ᴺ 🡒 native (Rew.embSubsts u ▹ φ)) :
    extended nativeTheory ⊢! (Rew.embSubsts e ▹ bounded t φ)ᴺ 🡒 native (Rew.embSubsts e ▹ bounded t φ) := by
  let r : Semisentence language (n+1) := .rel .lt ![#0, Rew.bShift t]
  let body : Semiproposition language 1 := (Rew.embSubsts e).q ▹ (r ⋏ φ)
  let u : Fin (n+1) → Term language ℕ := Fin.cases (&0) (fun i => Rew.shift (e i))
  have hrew : (Rew.free (L := language) (n := 0)).comp (Rew.embSubsts e).q = Rew.embSubsts u := by
    ext i
    · cases i using Fin.cases <;> simp [Rew.comp_app, Rew.q_embSubsts, u]
    · exact Empty.elim i
  have hgopen : (Rew.embSubsts u ▹ r).Open := by simp [r, Semiformula.Open]
  have hg := backward (Rew.embSubsts u ▹ r) (openAtoms _ hgopen)
  have hc := hback u
  have hconj := Entailment.CK_of_C_of_C (Entailment.C_trans Entailment.and₁ hg)
    (Entailment.C_trans Entailment.and₂ hc)
  have hfree : extended nativeTheory ⊢! Rewriting.free (bodyᴺ) 🡒 Rewriting.free (native body) := by
    simpa [body, native_rew, Semiformula.rew_doubleNegation, Rewriting.free,
      ← TransitiveRewriting.comp_app, hrew, IPRANativeFormula.native] using hconj
  have hcomp := existsCompare body hfree
  have hs := stableAnyBoundedExists t φ hφ e hback
  apply Entailment.C_trans ?_ hs
  simpa [bounded, bexs, body, r, IPRANativeFormula.native] using hcomp

end DiophantineConsistency.IPRABoundedLogic
