import PRAEqualityToIPRA
set_option autoImplicit false
noncomputable section
namespace PA194OpenFormulaTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRAStandardTheory
open IPRANativeFormula IPRANativeFormulaRew IPRATheoryHilbertBridge
open IPRABoundedInduction IPRAQuantifierFree
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem nativeOpenOfClassical {n : Nat} (φ : Semisentence language n) (hopen : φ.Open)
    (hp : PRA ⊢ ∀⁰* φ) : standardTheory ⊢ ∀⁰* native φ := by
  have hgg : nativeTheory ⊢! ∀⁰* φᴺ := by
    have ht := IPRAFullGGTransfer.from_classical hp
    have hpgg : nativeTheory ⊢ ∀⁰* φᴺ := by simpa [gg_allClosure] using ht
    exact Classical.choice hpgg
  apply (IPRAStandardTheory.provable_iff _).2
  apply Nonempty.intro
  apply IPRANativeDisjunctionWitness.closeFamily n (native φ)
  intro v
  have hinst := IPRATheoryInstantiation.instantiateTheory (T := nativeTheory) φᴺ hgg v
  have hback := IPRABoundedInduction.backward φ (Γ := 𝚺) (Hierarchy.of_open hopen) v
  have hinst' : extended nativeTheory ⊢! (Rew.embSubsts v ▹ φ)ᴺ := by
    simpa only [Semiformula.rew_doubleNegation] using hinst
  have hres := hback ⨀ hinst'
  simpa only [Semiformula.rew_doubleNegation, native_rew] using hres
#print axioms nativeOpenOfClassical
end PA194OpenFormulaTransfer
