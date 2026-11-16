import PA194UniqZeroQuote
import PA194TransitivitySyntax
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194UniqZeroSyntax
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardTyped PA194TransitivitySyntax PA194UniqZeroQuote

def equalZeroTerm {n : Nat} (x : Ordinal.Term n) : Ordinal.Formula n :=
  ∃⁰ ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (Rew.bShift (Rew.bShift x))) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ Ordinal.zero (.bvar 0)) ⋏ orderIso (.bvar 1) (.bvar 0)))

def bound : Ordinal.Formula 2 := equalZeroTerm (.bvar 1) 🡒
  (equalZeroTerm (.bvar 0) 🡒 equalTerm (.bvar 1) (.bvar 0))

theorem target_eq : formula uniqZero (Fin.elim0 : Fin 0 → Ordinal.Term 0)
    (fun _ : Nat => (.fvar 0 : Ordinal.Term 0)) =
  ∀⁰ (Ordinal.domain (.bvar 0) 🡒 ∀⁰ (Ordinal.domain (.bvar 0) 🡒 bound)) := by
  rfl

theorem equalZeroTerm_rew {n m : Nat} (τ : Rew language Nat n Nat m) (x : Ordinal.Term n) :
    Semiformula.rewAux τ (equalZeroTerm x) = equalZeroTerm (τ x) := by
  simp only [equalZeroTerm,Semiformula.rewAux,domain_rew,zero_rew,orderIso_rew,eq,
    Rew.q_bvar_zero,Rew.q_bvar_succ,Rew.q_comp_bShift_app,Ordinal.q_q_bvar_one]
  simp only [Function.comp_def,Matrix.comp_vecCons,Rew.q_comp_bShift_app,
    Rew.q_bvar_zero,Rew.q_bvar_succ,Ordinal.q_q_bvar_one]
  congr 6 <;> funext i <;> fin_cases i <;> rfl
#print axioms target_eq
#print axioms equalZeroTerm_rew
end PA194UniqZeroSyntax
