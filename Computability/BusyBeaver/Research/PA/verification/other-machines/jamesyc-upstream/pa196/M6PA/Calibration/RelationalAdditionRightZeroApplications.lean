module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightZeroSupplier
@[expose] public section

/-! Specialization of the closed right-zero conclusion at arbitrary parameters. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.zero
set_option maxHeartbeats 600000

def additionRightZeroApply {Γ : List Form} (x e r : Nat)
    (h : ND.Proof Γ addRightZeroStatement)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (he : ND.Proof Γ (Ordinal.zero (.fvar e)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar e) (.fvar r))) :
    ND.Proof Γ (orderIso (.fvar x) (.fvar r)) := by
  have hh : ND.Proof Γ (Ordinal.domain (.fvar x) 🡒 addRightZero (.fvar x)) := by
    convert allElim _ (.fvar x) h using 1 <;>
      ((try simp only [addRightZeroStatement]) <;> addRightZeroSyntax)
  exact addRightZeroAt x e r (mp hx hh) he hr

#print axioms additionRightZeroApply
end M6.PA.RelationalSource.PairGraph
