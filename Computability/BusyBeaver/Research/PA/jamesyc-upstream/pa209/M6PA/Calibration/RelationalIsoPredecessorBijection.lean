module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoPredecessorLaws
public import M6PA.Calibration.RelationalIsoPredecessorTotal
@[expose] public section

/-! All seven predecessor bijection clauses. The actual graph-entry premise
is retained and retyped, never inferred from decoded-edge typing alone. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def predecessorOrderBijection {Γ : List Form} (g a b p q h : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (hp : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a)))
    (hq : ND.Proof Γ (Ordinal.successor (.fvar q) (.fvar b)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q)))
    (entries : ND.Proof Γ (graphEntries (.fvar h) (.fvar p) (.fvar b)))
    (restriction : ND.Proof Γ (strictGraphRestriction (.fvar p) (.fvar g) (.fvar h))) :
    ND.Proof Γ (orderBijection (.fvar h) (.fvar p) (.fvar q)) := by
  have leftTotal := andLeft (andRight (andRight hg))
  have rightTotal := andLeft (andRight (andRight (andRight hg)))
  have functional := andLeft (andRight (andRight (andRight (andRight hg))))
  have injective := andLeft (andRight (andRight (andRight (andRight (andRight hg)))))
  have ordered := andRight (andRight (andRight (andRight (andRight (andRight hg)))))
  exact andIntro (predecessorGraphEntries g h p q b ordered restriction he entries)
    (andIntro (predecessorGraphTyped g h p q ordered restriction he)
      (andIntro (predecessorGraphLeftTotal g h a p leftTotal hp restriction)
        (andIntro (predecessorGraphRightTotal g h b p q rightTotal ordered hq restriction he)
          (andIntro (predecessorGraphFunctional g h p functional restriction)
            (andIntro (predecessorGraphInjective g h p injective restriction)
              (predecessorGraphOrder g h p ordered restriction))))))

#print axioms predecessorOrderBijection
end M6.PA.RelationalSource.PairGraph
