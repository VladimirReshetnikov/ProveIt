import PA194AdditionRestrictionRecurrence
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def restrictionPrefix {Γ : List Form} (E : FormulaEquality Γ) (t u base e g h : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hp : ND.Proof Γ (addPrefix (.fvar u) (.fvar base) (.fvar e) (.fvar g)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h))) :
    ND.Proof Γ (addPrefix (.fvar t) (.fvar base) (.fvar e) (.fvar h)) := by
  have hd := andLeft hp
  have hf := andLeft (andRight hp)
  have hg := andLeft (andRight (andRight hp))
  have he := andLeft (andRight (andRight (andRight hp)))
  have hc := andRight (andRight (andRight (andRight hp)))
  have hi := mp (outputIntro g e base he) (andLeft (graphDomainAt u g e hd))
  exact andIntro (restrictionDomain t u g h hs hd hr)
    (andIntro (restrictionFunctional t g h hr hf)
      (andIntro (restrictionRange t g h hr hg)
        (andIntro (restrictionIntro t g h e base hr he (restrictionZeroInside E t u e hs hz hi))
          (restrictionRecurrence E t g h ht hr hc))))

#print axioms restrictionPrefix
end M6.PA.RelationalSource.PairGraph
