import PA194ForwardTyped
import PA194PAeqTargetInventory
import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194TransitivitySyntax
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardTyped

def equalTerm {n : Nat} (x y : Ordinal.Term n) : Ordinal.Formula n :=
  ∃⁰ ∃⁰ ((Ordinal.domain (.bvar 1) ⋏ eq (.bvar 1) (Rew.bShift (Rew.bShift x))) ⋏
    ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (Rew.bShift (Rew.bShift y))) ⋏ orderIso (.bvar 1) (.bvar 0)))

def bound : Ordinal.Formula 3 := equalTerm (.bvar 2) (.bvar 1) 🡒
  (equalTerm (.bvar 1) (.bvar 0) 🡒 equalTerm (.bvar 2) (.bvar 0))

theorem target_eq : formula PA194PAeq.transitivity (Fin.elim0 : Fin 0 → Ordinal.Term 0)
    (fun _ : Nat => (.fvar 0 : Ordinal.Term 0)) =
  ∀⁰ (Ordinal.domain (.bvar 0) 🡒 ∀⁰ (Ordinal.domain (.bvar 0) 🡒 ∀⁰ (Ordinal.domain (.bvar 0) 🡒 bound))) := by
  rfl

theorem equalTerm_rew {n m : Nat} (τ : Rew language Nat n Nat m) (x y : Ordinal.Term n) :
    Semiformula.rewAux τ (equalTerm x y) = equalTerm (τ x) (τ y) := by
  simp only [equalTerm,Semiformula.rewAux,domain_rew,orderIso_rew,eq,
    Rew.q_bvar_zero,Rew.q_bvar_succ,Rew.q_comp_bShift_app,Ordinal.q_q_bvar_one]
  simp only [Function.comp_def,Matrix.comp_vecCons,Rew.q_comp_bShift_app,
    Rew.q_bvar_zero,Rew.q_bvar_succ,Ordinal.q_q_bvar_one]
  congr 6 <;> funext i <;> fin_cases i <;> rfl
#print axioms target_eq
#print axioms equalTerm_rew
end PA194TransitivitySyntax
