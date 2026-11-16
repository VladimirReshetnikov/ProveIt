module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionZeroLaw
public import M6PA.Calibration.RelationalMultiplicationZeroLaw
public import M6PA.Calibration.RelationalOrderIsoTransport
public import M6PA.Calibration.RelationalZeroIso
@[expose] public section

/-! The two arithmetic zero equations in the interpreted equality relation.
No arbitrary empty representative is identified by raw equality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def additionZeroLawIso {Γ : List Form} (E : FormulaEquality Γ) (x b out : Nat)
    (hidentity : ND.Proof Γ identityStatement)
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hp : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar out))) :
    ND.Proof Γ (orderIso (.fvar out) (.fvar b)) :=
  orderIsoLeftTransport E b out b (E.symmetryOf (addResultZeroOutput E x b out hz hp))
    (orderIsoFromExists E b (identityAt b hidentity hb))

def multiplicationZeroLawIso {Γ : List Form} (E : FormulaEquality Γ) (x b out z : Nat)
    (hx : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hz : ND.Proof Γ (Ordinal.zero (.fvar z)))
    (hp : ND.Proof Γ (mulResult (.fvar x) (.fvar b) (.fvar out))) :
    ND.Proof Γ (orderIso (.fvar out) (.fvar z)) :=
  zeroOrderIso E out z (mulResultZeroOutput E x b out hx hp) hz

#print axioms additionZeroLawIso
#print axioms multiplicationZeroLawIso
end M6.PA.RelationalSource.PairGraph
