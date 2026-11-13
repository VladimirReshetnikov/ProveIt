import DiophantineConsistency.Sign14Positive74ObjectShiftToPositiveOpen

/-! SOURCE ONLY: bind the canonical fourteen open variables back to a sentence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectCloseBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory IPRANativeTheory
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (PRAFiniteFunctionCodes.Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def freeVec : Fin 14 → Term language ℕ := fun i => &i.val

theorem bindRew14 : (Rew.fixitr 0 14).comp (Rew.embSubsts freeVec) =
    (Rew.emb : Rew language Empty 14 ℕ 14) := by
  ext i
  · change (Rew.fixitr 0 14) (&i.val : SyntacticTerm language) = #i
    rw [Rew.fixitr_fvar, dif_pos i.isLt]
    congr 1
    apply Fin.ext
    simp
  · exact Empty.elim i

theorem bindSentence14 (φ : Semisentenceᵢ language 14) :
    (∀⁰* (Rew.fixitr 0 14 ▹ (Rew.embSubsts freeVec ▹ φ))) =
      Rewriting.emb (∀⁰* φ) := by
  simp only [← TransitiveRewriting.comp_app, bindRew14, Rewriting.emb_allClosure]
end DiophantineConsistency.Sign14Positive74ObjectCloseBind
#print axioms DiophantineConsistency.Sign14Positive74ObjectCloseBind.bindRew14
#print axioms DiophantineConsistency.Sign14Positive74ObjectCloseBind.bindSentence14
