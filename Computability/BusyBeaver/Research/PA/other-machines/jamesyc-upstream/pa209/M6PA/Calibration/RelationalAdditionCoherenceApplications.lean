module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCoherenceSupplier
public import M6PA.Calibration.RelationalOrderIsoReflexivity
@[expose] public section

/-! Applications of the paid full two-input coherence sentence. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain
set_option maxHeartbeats 600000

def additionCoherenceApply {Γ : List Form} (x y b c r s : Nat)
    (h : ND.Proof Γ addCoherenceStatement)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hy : ND.Proof Γ (Ordinal.domain (.fvar y)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hc : ND.Proof Γ (Ordinal.domain (.fvar c)))
    (hxy : ND.Proof Γ (orderIso (.fvar x) (.fvar y)))
    (hbc : ND.Proof Γ (orderIso (.fvar b) (.fvar c)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (addResult (.fvar y) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  have hh : ND.Proof Γ (Ordinal.domain (.fvar x) 🡒 addCoherence (.fvar x)) := by
    convert allElim _ (.fvar x) h using 1 <;>
      ((try simp only [addCoherenceStatement]) <;> coherenceInductionSyntax)
  exact mp (andIntro hy (andIntro hb (andIntro hc
    (andIntro hxy (andIntro hbc (andIntro hr hs))))))
    (addCoherenceAt x y b c r s (mp hx hh))

def additionOutputUniqueUpToIso {Γ : List Form} (E : FormulaEquality Γ)
    (x b r s : Nat) (hidentity : ND.Proof Γ identityStatement)
    (hcoherence : ND.Proof Γ addCoherenceStatement)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hr : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) :=
  additionCoherenceApply x x b b r s hcoherence hx hx hb hb
    (orderIsoFromExists E x (identityAt x hidentity hx))
    (orderIsoFromExists E b (identityAt b hidentity hb)) hr hs

#print axioms additionCoherenceApply
#print axioms additionOutputUniqueUpToIso
end M6.PA.RelationalSource.PairGraph
