import PA194SuccValueElimination
import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194SuccInjective
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def succValueTerm {n : Nat} (x z : Ordinal.Term n) : Ordinal.Formula n := Ordinal.domain z ⋏
  (∃⁰ ((Ordinal.domain (.bvar 0) ⋏ eq (.bvar 0) (Rew.bShift x)) ⋏
    Ordinal.successor (.bvar 0) (Rew.bShift z)))

theorem succValueTerm_rew {n m : Nat} (τ : Rew language Nat n Nat m) (x z : Ordinal.Term n) :
    Semiformula.rewAux τ (succValueTerm x z) = succValueTerm (τ x) (τ z) := by
  simp only [succValueTerm,Semiformula.rewAux,domain_rew,successor_rew,eq,
    Rew.q_bvar_zero,Rew.q_comp_bShift_app]
  simp only [Function.comp_def,Matrix.comp_vecCons,Rew.q_comp_bShift_app,Rew.q_bvar_zero]
  congr 6 <;> funext i <;> fin_cases i <;> rfl

theorem succValueTerm_fvar (x z : Nat) : succValueTerm (.fvar x) (.fvar z) = succValue x z := rfl

def succEqualAt (x y : Nat) : Form := ∃⁰ ∃⁰
  (succValueTerm (.fvar x) (.bvar 1) ⋏
    (succValueTerm (.fvar y) (.bvar 0) ⋏ orderIso (.bvar 1) (.bvar 0)))

theorem succEqualAt_shift (x y : Nat) : (succEqualAt x y).shift = succEqualAt (x+1) (y+1) := by
  change Semiformula.rewAux Rew.shift (succEqualAt x y) = _
  simp [succEqualAt,Semiformula.rewAux,succValueTerm_rew,orderIso_rew,Rew.shift,Rew.map,Rew.q]
#print axioms succValueTerm_rew
#print axioms succValueTerm_fvar
#print axioms succEqualAt_shift
end PA194SuccInjective
