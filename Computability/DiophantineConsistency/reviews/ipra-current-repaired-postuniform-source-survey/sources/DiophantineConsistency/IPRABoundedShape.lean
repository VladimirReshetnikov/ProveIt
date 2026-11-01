import DiophantineConsistency.IPRABoundedChild
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRABoundedShape
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenFormulaCompiler
open IPRANativeFormula IPRANativeTheory IPRATheoryHilbertBridge IPRABoundedChild IPRACharacteristicTransfer
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def bounded {n : ℕ} (t : TermN n) (φ : Semisentence language (n+1)) : Semisentence language n :=
  ∃⁰[(Semiformula.rel Language.ORing.Rel.lt ![#0, Rew.bShift t])] φ

theorem shape {n : ℕ} (t : TermN n) (φ : Semisentence language (n+1))
    (e : Fin n → Term language ℕ) :
    native (Rew.embSubsts e ▹ bounded t φ) =
      ∃⁰ (guard (Fin.cases (Rew.embSubsts e t) e) ⋏ childBody φ (Fin.cases (Rew.embSubsts e t) e)) := by
  simp [bounded, bexs, IPRANativeFormula.native, IPRABoundedChild.guard, childBody, assign]
  constructor
  · rfl
  · have hrew : (Rew.embSubsts e).q = Rew.embSubsts (Fin.cases (#0) (fun i => Rew.bShift (e i))) := by
      ext i
      · cases i using Fin.cases <;> simp [Rew.q_embSubsts]
      · exact Empty.elim i
    rw [hrew]
def stableBoundedExists {n : ℕ} (t : TermN n) (φ : Semisentence language (n+1))
    (hφ : Hierarchy 𝚺 0 φ) (e : Fin n → Term language ℕ)
    (hback : ∀ u : Fin (n+1) → Term language ℕ,
      extended nativeTheory ⊢! (Rew.embSubsts u ▹ φ)ᴺ 🡒 native (Rew.embSubsts u ▹ φ)) :
    extended nativeTheory ⊢! ∼∼native (Rew.embSubsts e ▹ bounded t φ) 🡒 native (Rew.embSubsts e ▹ bounded t φ) := by
  simpa only [shape] using stableFromBounded φ hφ (Fin.cases (Rew.embSubsts e t) e) hback
theorem boundedCharacteristicAny {Γ : Polarity} {n : ℕ} (φ : Semisentence language n)
    (hφ : Hierarchy Γ 0 φ) : ∃ c : Code n,
      PRA ⊢ PRACharacteristicBit.bitSentence c ∧ PRA ⊢ PRABoundedCharacteristic.oneCorrectSentence c φ := by
  obtain ⟨p, hp⟩ := PRABoundedFormula.representAux hφ rfl
  subst φ
  obtain ⟨c, _, hb, hc⟩ := PRABoundedFormula.hasCharacteristic p
  exact ⟨c, hb, hc⟩

def decideBoundedFromBackward {Γ : Polarity} {n : ℕ} (φ : Semisentence language n)
    (hφ : Hierarchy Γ 0 φ) (e : Fin n → Term language ℕ)
    (hback : extended nativeTheory ⊢! (Rew.embSubsts e ▹ φ)ᴺ 🡒 native (Rew.embSubsts e ▹ φ)) :
    extended nativeTheory ⊢! native (Rew.embSubsts e ▹ φ) ⋎ ∼native (Rew.embSubsts e ▹ φ) := by
  let h := boundedCharacteristicAny φ hφ
  let c := Classical.choose h
  have hc := Classical.choose_spec h
  exact decideFromCharacteristic c φ hc.2 e hback
end DiophantineConsistency.IPRABoundedShape
