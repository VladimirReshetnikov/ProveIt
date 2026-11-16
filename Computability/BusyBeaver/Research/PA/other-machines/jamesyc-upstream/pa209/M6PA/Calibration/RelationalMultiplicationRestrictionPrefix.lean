module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationRestrictionRecurrence
@[expose] public section

/-! Restriction of a full multiplication prefix, preserving its original literal zero.
The graph restriction premise is discharged by actual Separation in the witness
supplier; no abstract restriction axiom is added. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def mulRestrictionPrefix {Γ : List Form} (E : FormulaEquality Γ) (t u base e g h : Nat)
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar t) (.fvar u)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hp : ND.Proof Γ (mulPrefix (.fvar u) (.fvar base) (.fvar e) (.fvar g)))
    (hr : ND.Proof Γ (graphRestriction (.fvar t) (.fvar g) (.fvar h))) :
    ND.Proof Γ (mulPrefix (.fvar t) (.fvar base) (.fvar e) (.fvar h)) := by
  have hd := andLeft hp
  have hf := andLeft (andRight hp)
  have hg := andLeft (andRight (andRight hp))
  have he := andLeft (andRight (andRight (andRight hp)))
  have hc := andRight (andRight (andRight (andRight hp)))
  have hi := mp (outputIntro g e e he) (andLeft (graphDomainAt u g e hd))
  exact andIntro (restrictionDomain t u g h hs hd hr)
    (andIntro (restrictionFunctional t g h hr hf)
      (andIntro (restrictionRange t g h hr hg)
        (andIntro (restrictionIntro t g h e e hr he (restrictionZeroInside E t u e hs hz hi))
          (mulRestrictionRecurrence E t g h base ht hr hc))))

#print axioms mulRestrictionPrefix
end M6.PA.RelationalSource.PairGraph
