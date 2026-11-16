module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCommutativitySupplier
@[expose] public section

/-! Explicit specialization of constructive commutativity. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain
set_option maxHeartbeats 800000

def additionCommutativityApply {Γ : List Form} (x y r s : Nat)
    (h : ND.Proof Γ addCommutativityStatement)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hy : ND.Proof Γ (Ordinal.domain (.fvar y)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar y) (.fvar r)))
    (hs : ND.Proof Γ (addResult (.fvar y) (.fvar x) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  have hh : ND.Proof Γ (Ordinal.domain (.fvar x) 🡒 addCommutativity (.fvar x)) := by
    convert allElim _ (.fvar x) h using 1 <;>
      ((try simp only [addCommutativityStatement]) <;> addCommutativitySyntax)
  exact mp (andIntro hy (andIntro hr hs)) (addCommutativityAt x y r s (mp hx hh))

def additionCommutativityClosedShift {Γ : List Form}
    (h : ND.Proof Γ addCommutativityStatement) :
    ND.Proof (shifted Γ) addCommutativityStatement := by
  convert shiftProof h using 1 <;>
    ((try simp only [addCommutativityStatement]) <;> addCommutativitySyntax)

#print axioms additionCommutativityApply
#print axioms additionCommutativityClosedShift
end M6.PA.RelationalSource.PairGraph
