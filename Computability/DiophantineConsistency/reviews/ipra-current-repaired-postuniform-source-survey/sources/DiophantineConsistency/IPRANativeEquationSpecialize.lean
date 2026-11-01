import DiophantineConsistency.IPRAAllSpecialize
set_option autoImplicit false
namespace DiophantineConsistency.IPRANativeEquationSpecialize
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRALanguage PRATheory IPRANativeTheory IPRAAllSpecialize
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def equal (a b : SyntacticTerm language) : Propositionᵢ language :=
  Semiformulaᵢ.rel Language.ORing.Rel.eq ![a,b]

theorem specialize_equalClosureI {n : ℕ} (a b : TermN n)
    (v : Fin n → SyntacticTerm language) (Γ : List (Propositionᵢ language))
    (h : Γ ⊢[(𝗜𝗻𝘁¹ : Hilbertᵢ language)] Rewriting.emb (equalClosureI a b)) :
    Γ ⊢[𝗜𝗻𝘁¹] equal (Rew.subst v (Rew.emb a)) (Rew.subst v (Rew.emb b)) := by
  let p : Semiformulaᵢ language ℕ n := Rewriting.emb (Semiformulaᵢ.rel Language.ORing.Rel.eq ![a,b] : Semisentenceᵢ language n)
  have hclosed : Γ ⊢[𝗜𝗻𝘁¹] ∀⁰* p := by
    simpa only [equalClosureI, p, Rewriting.emb_allClosure] using h
  have hs := specialize_over_context p v Γ hclosed
  convert hs using 1
  simp [p, equal, Rewriting.subst, Semiformulaᵢ.rew_rel]
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
end DiophantineConsistency.IPRANativeEquationSpecialize
