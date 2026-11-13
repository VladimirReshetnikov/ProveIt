module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionZeroLaw
public import M6PA.Calibration.RelationalOrderIsoTransport
public import M6PA.Calibration.RelationalOrderIsoZero
@[expose] public section

/-! The zero case of two-input addition coherence. Both result witnesses are
actual traces; only their raw output equality is used to transport the given
base isomorphism. No canonical empty representative is chosen. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] orderIso addResult

def additionZeroCoherence {Γ : List Form} (E : FormulaEquality Γ)
    (x y b c r s : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar x)))
    (hxy : ND.Proof Γ (orderIso (.fvar x) (.fvar y)))
    (hbc : ND.Proof Γ (orderIso (.fvar b) (.fvar c)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (addResult (.fvar y) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  have hy := orderIsoZeroForward x y hz hxy
  have er := addResultZeroOutput E x b r hz hr
  have es := addResultZeroOutput E y c s hy hs
  have hrc := orderIsoLeftTransport E b r c (E.symmetryOf er) hbc
  exact orderIsoRightTransport E r c s (E.symmetryOf es) hrc

#print axioms additionZeroCoherence
end M6.PA.RelationalSource.PairGraph
