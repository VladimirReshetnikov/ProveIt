import PA194SuccInjectiveValue
import PA194TransitivitySyntax
import PA194ForwardTyped
import PA194PAeqTargetInventory
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccInjective
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194ForwardTyped PA194TransitivitySyntax PA194InverseEqual

def succEqualTerm {n : Nat} (x y : Ordinal.Term n) : Ordinal.Formula n := ∃⁰ ∃⁰
  (succValueTerm (Rew.bShift (Rew.bShift x)) (.bvar 1) ⋏
    (succValueTerm (Rew.bShift (Rew.bShift y)) (.bvar 0) ⋏ orderIso (.bvar 1) (.bvar 0)))

theorem succEqualTerm_rew {n m : Nat} (τ : Rew language Nat n Nat m) (x y : Ordinal.Term n) :
    Semiformula.rewAux τ (succEqualTerm x y) = succEqualTerm (τ x) (τ y) := by
  simp only [succEqualTerm,Semiformula.rewAux,succValueTerm_rew,orderIso_rew,
    Rew.q_bvar_zero,Rew.q_bvar_succ,Rew.q_comp_bShift_app,Ordinal.q_q_bvar_one]

theorem succEqualTerm_fvar (x y : Nat) : succEqualTerm (.fvar x) (.fvar y) = succEqualAt x y := rfl

def bound : Ordinal.Formula 2 := succEqualTerm (.bvar 1) (.bvar 0) 🡒 equalTerm (.bvar 1) (.bvar 0)

theorem target_eq : formula PA194PAeq.succInjective (Fin.elim0 : Fin 0 → Ordinal.Term 0)
    (fun _ : Nat => (.fvar 0 : Ordinal.Term 0)) =
  ∀⁰ (Ordinal.domain (.bvar 0) 🡒 ∀⁰ (Ordinal.domain (.bvar 0) 🡒 bound)) := by
  rfl
#print axioms succEqualTerm_rew
#print axioms succEqualTerm_fvar
#print axioms target_eq
end PA194SuccInjective
