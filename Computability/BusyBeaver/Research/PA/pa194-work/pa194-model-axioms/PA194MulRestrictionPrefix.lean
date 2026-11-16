import PA194MulRestrictionRecurrence
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

def restrictionPrefix {Γ : List Form} (E : FormulaEquality Γ) (t u base e g h : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hp : ND.Proof Γ (mulPrefix (.fvar u) (.fvar base) (.fvar e) (.fvar g)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h))) :
    ND.Proof Γ (mulPrefix (.fvar t) (.fvar base) (.fvar e) (.fvar h)) := by
  have hd := ND.andLeft hp
  have hf := ND.andLeft (ND.andRight hp)
  have hg := ND.andLeft (ND.andRight (ND.andRight hp))
  have he := ND.andLeft (ND.andRight (ND.andRight (ND.andRight hp)))
  have hc := ND.andRight (ND.andRight (ND.andRight (ND.andRight hp)))
  have hi := ND.mp (outputIntro g e e he) (ND.andLeft (graphDomainAt u g e hd))
  exact ND.andIntro (restrictionDomain t u g h hs hd hr)
    (ND.andIntro (restrictionFunctional t g h hr hf)
      (ND.andIntro (restrictionRange t g h hr hg)
        (ND.andIntro (restrictionIntro t g h e e hr he (restrictionZeroInside E t u e hs hz hi))
          (restrictionRecurrence E t g h base ht hr hc))))
#print axioms restrictionPrefix
end PA194MulRecurrenceNew
