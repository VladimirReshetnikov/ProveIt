module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoSuccessorEntries
public import M6PA.Calibration.RelationalIsoSuccessorTotal
public import M6PA.Calibration.RelationalIsoSuccessorInjective
public import M6PA.Calibration.RelationalIsoSuccessorOrder
@[expose] public section

/-! All seven clauses of a genuine successor order-bijection. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def successorOrderBijection {Γ : List Form} (E : FormulaEquality Γ) (g p h a b c d : Nat)
    (hg : ND.Proof Γ (orderBijection (.fvar g) (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar c)))
    (ht : ND.Proof Γ (Ordinal.successor (.fvar b) (.fvar d)))
    (hadj : ND.Proof Γ (adjunction (.fvar g) (.fvar p) (.fvar h)))
    (hpair : ND.Proof Γ (kuratowski (.fvar p) (.fvar a) (.fvar b))) :
    ND.Proof Γ (orderBijection (.fvar h) (.fvar c) (.fvar d)) := by
  have entries := andLeft hg
  have typed := andLeft (andRight hg)
  have leftTotal := andLeft (andRight (andRight hg))
  have rightTotal := andLeft (andRight (andRight (andRight hg)))
  have functional := andLeft (andRight (andRight (andRight (andRight hg))))
  have injective := andLeft (andRight (andRight (andRight (andRight (andRight hg)))))
  have ordered := andRight (andRight (andRight (andRight (andRight (andRight hg)))))
  have exactGraph := adjunctionExact E.core E.transitive g p h a b hadj hpair
  exact andIntro (successorTwoGraphEntries E.core g p h a b c d entries hs ht hadj hpair)
    (andIntro (successorGraphTyped E g h a b c d typed hs ht exactGraph)
      (andIntro (successorGraphLeftTotal E g h a b c leftTotal hs exactGraph)
        (andIntro (successorGraphRightTotal E g h a b d rightTotal ht exactGraph)
          (andIntro (functionalExtension E g h a b functional exactGraph (typedNoEndpointOutput g a b typed ha))
            (andIntro (successorGraphInjective E g h a b typed hb injective exactGraph)
              (successorGraphOrder E g h a b typed ha hb ordered exactGraph))))))

#print axioms successorOrderBijection
end M6.PA.RelationalSource.PairGraph
