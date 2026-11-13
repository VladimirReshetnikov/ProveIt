module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIsoReflexivity
@[expose] public section

/-! Ordinary equality transports the endpoints of a witnessed isomorphism.
This does not identify merely isomorphic representatives as equal. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] orderIso
set_option maxHeartbeats 600000

def orderIsoRightTransport {Γ : List Form} (E : FormulaEquality Γ) (a b c : Nat)
    (hbc : ND.Proof Γ (eq (.fvar b) (.fvar c)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar c)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar b]) (orderIso (.fvar a) (.bvar 0))) := by
    convert hi using 1 <;> isoSyntax
  have out := E.substituteOne (orderIso (.fvar a) (.bvar 0)) (.fvar b) (.fvar c) hbc hp
  convert out using 1 <;> isoSyntax

def orderIsoLeftTransport {Γ : List Form} (E : FormulaEquality Γ) (a b c : Nat)
    (hab : ND.Proof Γ (eq (.fvar a) (.fvar b)))
    (hi : ND.Proof Γ (orderIso (.fvar a) (.fvar c))) :
    ND.Proof Γ (orderIso (.fvar b) (.fvar c)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar a]) (orderIso (.bvar 0) (.fvar c))) := by
    convert hi using 1 <;> isoSyntax
  have out := E.substituteOne (orderIso (.bvar 0) (.fvar c)) (.fvar a) (.fvar b) hab hp
  convert out using 1 <;> isoSyntax

def orderIsoFromEquality {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (hidentity : ND.Proof Γ identityStatement)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hab : ND.Proof Γ (eq (.fvar a) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar a) (.fvar b)) :=
  orderIsoRightTransport E a a b hab
    (orderIsoFromExists E a (identityAt a hidentity ha))

#print axioms orderIsoRightTransport
#print axioms orderIsoLeftTransport
#print axioms orderIsoFromEquality
end M6.PA.RelationalSource.PairGraph
