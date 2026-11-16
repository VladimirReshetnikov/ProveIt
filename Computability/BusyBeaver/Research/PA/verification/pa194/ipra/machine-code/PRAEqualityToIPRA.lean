import DiophantineConsistency.IPRABoundedInduction
import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.IPRANativeDisjunctionWitness
import DiophantineConsistency.IPRAStandardTheory
set_option autoImplicit false
noncomputable section
namespace PRAEqualityToIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRAStandardTheory
open IPRANativeFormula IPRANativeFormulaRew IPRATheoryHilbertBridge
open IPRABoundedInduction IPRAQuantifierFree
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

/-- A universally quantified PR-code equality provable in candidate classical
PRA is provable in its native intuitionistic counterpart. -/
theorem nativeOfClassical {n : ℕ} (a b : TermN n) (hp : PRA ⊢ equalClosure a b) :
    standardTheory ⊢ equalClosureI a b := by
  let φ : Semisentence language n := .rel Language.ORing.Rel.eq ![a,b]
  have hgg : nativeTheory ⊢! ∀⁰* φᴺ := by
    have ht := IPRAFullGGTransfer.from_classical hp
    have hpgg : nativeTheory ⊢ ∀⁰* φᴺ := by simpa [equalClosure,φ,gg_allClosure] using ht
    exact Classical.choice hpgg
  apply (IPRAStandardTheory.provable_iff _).2
  apply Nonempty.intro
  change nativeTheory ⊢! ∀⁰* native φ
  apply IPRANativeDisjunctionWitness.closeFamily n (native φ)
  intro v
  have hinst := IPRATheoryInstantiation.instantiateTheory (T := nativeTheory) φᴺ hgg v
  have hback := IPRABoundedInduction.backward φ (Γ := 𝚺) (Hierarchy.rel _ _ _ _) v
  have hres := hback ⨀ hinst
  simpa only [Semiformula.rew_doubleNegation, native_rew] using hres

#print axioms nativeOfClassical
end PRAEqualityToIPRA
