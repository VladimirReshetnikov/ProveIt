import PA194FoundationGraphOperations

/-! An addition trace with an empty input has its unique output equal to the
base. The displayed zero object is forced equal by the actual inclusive domain,
not by extensionality or a canonical-empty assumption. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def addPrefixZeroOutput {Γ : List Form} (E : FormulaEquality Γ) (x base e g out : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hp : ND.Proof Γ (addPrefix (.fvar x) (.fvar base) (.fvar e) (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar out))) :
    ND.Proof Γ (eq (.fvar out) (.fvar base)) := by
  have domain := andLeft hp
  have functional := andLeft (andRight hp)
  have zeroEdge := andLeft (andRight (andRight (andRight hp)))
  have cases := mp (outputIntro g e base zeroEdge) (andLeft (graphDomainAt x g e domain))
  have equality : ND.Proof Γ (eq (.fvar e) (.fvar x)) := by
    apply orElim cases
    · exact botElim (contradiction (assumption (by simp)) (up (Ordinal.zeroNotMem x e hz) _))
    · exact assumption (by simp)
  exact graphFunctionalAt g x out base functional he
    (edgeInputTransport E g e x base equality zeroEdge)

#print axioms addPrefixZeroOutput
end M6.PA.RelationalSource.PairGraph
