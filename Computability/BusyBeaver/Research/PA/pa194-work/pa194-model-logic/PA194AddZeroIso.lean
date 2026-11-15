import PA194ForwardReflProof
import PA194FoundationAdditionZeroLaw
import PA194FoundationAdditionOutputExists
import PA194OrderIsoRew
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ForwardAddZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
variable {Γ : List Form}

def isoOfEqual (x y : Nat) (E : FormulaEquality Γ)
    (hxy : ND.Proof Γ (eq (.fvar x) (.fvar y)))
    (hi : ND.Proof Γ (orderIso (.fvar y) (.fvar y))) :
    ND.Proof Γ (orderIso (.fvar x) (.fvar y)) := by
  let P : Ordinal.Formula 1 := orderIso (.bvar 0) (.fvar y)
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar y]) P) := by
    simpa [P,orderIso_rew,Rew.subst] using hi
  have hh := E.substituteOne P (.fvar y) (.fvar x) (E.symmetryOf hxy) hp
  simpa [P,orderIso_rew,Rew.subst] using hh
def isoOfZeroAdd (a b out : Nat) (E : FormulaEquality Γ)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hr : ND.Proof Γ (addResult (.fvar a) (.fvar b) (.fvar out)))
    (hi : ND.Proof Γ (orderIso (.fvar b) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar out) (.fvar b)) :=
  isoOfEqual out b E (addResultZeroOutput E a b out hz hr) hi
def outputOfZeroAdd (a b : Nat) (E : FormulaEquality Γ)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (addOutput (.fvar a) (.fvar b)) :=
  addOutputFromExists E a b (zeroPrefixWitness E a b hz hb hempty hadj)
#print axioms outputOfZeroAdd
#print axioms isoOfZeroAdd
#print axioms isoOfEqual
end PA194ForwardAddZero
