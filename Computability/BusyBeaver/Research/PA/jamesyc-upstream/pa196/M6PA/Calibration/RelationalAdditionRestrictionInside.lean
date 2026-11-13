module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRecurrence
public import M6PA.Calibration.RelationalGraphRestrictionInclusiveDomain
public import M6PA.Calibration.RelationalGraphRestrictionInclusiveLaws
@[expose] public section

/-! Inclusive trace restriction retains the literal empty witness and every
predecessor input. These are ordinary finite ND derivations. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def restrictionZeroInside {Γ : List Form} (E : FormulaEquality Γ) (t u e : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hi : ND.Proof Γ (inclusiveDomain (.fvar u) (.fvar e))) :
    ND.Proof Γ (inclusiveDomain (.fvar t) (.fvar e)) := by
  apply orElim hi
  · exact mp (assumption (by simp)) (up (andLeft (Ordinal.successorAt t u e hs)) _)
  · have hu := successorMember E.core t u hs
    let q : Form := eq (.fvar e) (.fvar u)
    have he := Ordinal.memContainer (E.core.up q) u e t
      (Ordinal.eqSymm (E.core.up q) e u (assumption (by simp [q]))) (up hu q)
    exact botElim (contradiction he (up (Ordinal.zeroNotMem e t hz) _))

def restrictionPredecessorInside {Γ : List Form} (E : FormulaEquality Γ) (t i j : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hi : ND.Proof Γ (inclusiveDomain (.fvar t) (.fvar i)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar j) (.fvar i))) :
    ND.Proof Γ (inclusiveDomain (.fvar t) (.fvar j)) := by
  have hj := successorMember E.core j i hs
  apply orElim hi
  · exact ND.orLeft (Ordinal.transitiveAt t i j (up (andLeft (andLeft ht)) _)
      (assumption (by simp)) (up hj _))
  · exact ND.orLeft (Ordinal.memContainer (E.core.up _) i t j
      (assumption (by simp)) (up hj _))

#print axioms restrictionZeroInside
#print axioms restrictionPredecessorInside
end M6.PA.RelationalSource.PairGraph
