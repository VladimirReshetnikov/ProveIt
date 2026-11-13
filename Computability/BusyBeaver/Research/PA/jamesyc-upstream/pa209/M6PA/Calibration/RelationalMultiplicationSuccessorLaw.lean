module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceApplications
public import M6PA.Calibration.RelationalMultiplicationCoherenceOutputRight
@[expose] public section

/-! The first-argument multiplicative recursion equation modulo actual
isomorphism, comparing independently witnessed product and sum traces. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)
attribute [local irreducible] addResult mulResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

def multiplicationCoherenceClosedShift {Γ : List Form}
    (h : ND.Proof Γ mulCoherenceStatement) : ND.Proof (shifted Γ) mulCoherenceStatement := by
  convert shiftProof h using 1 <;>
    ((try simp only [mulCoherenceStatement]) <;> mulCoherenceInductionSyntax)

def multiplicationSuccessorLaw {Γ : List Form} (E : FormulaEquality Γ)
    (x u b r s out : Nat)
    (hsep : ND.Proof Γ closedInclusiveSeparation)
    (hidentity : ND.Proof Γ identityStatement)
    (hadd : ND.Proof Γ addCoherenceStatement)
    (hmul : ND.Proof Γ mulCoherenceStatement)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hr : ND.Proof Γ (Ordinal.domain (.fvar r)))
    (hxu : ND.Proof Γ (Ordinal.successor (.fvar x) (.fvar u)))
    (hxr : ND.Proof Γ (mulResult (.fvar x) (.fvar b) (.fvar r)))
    (hrs : ND.Proof Γ (addResult (.fvar r) (.fvar b) (.fvar s)))
    (huo : ND.Proof Γ (mulResult (.fvar u) (.fvar b) (.fvar out))) :
    ND.Proof Γ (orderIso (.fvar s) (.fvar out)) := by
  have hxx := orderIsoFromExists E x (identityAt x hidentity hx)
  have hbb := orderIsoFromExists E b (identityAt b hidentity hb)
  apply exsElim (mulResultPredecessor E x u b out hsep hx hxu huo)
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (mulResult (.fvar x) (.fvar b) (.bvar 0) ⋏ addResult (.bvar 0) (.fvar b) (.fvar out))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (mulResult (.fvar (x+1)) (.fvar (b+1)) (.fvar 0) ⋏
        addResult (.fvar 0) (.fvar (b+1)) (.fvar (out+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> mulCoherenceWitnessSyntax)
  have dx := up (Ordinal.domainShift x hx) body.free
  have db := up (Ordinal.domainShift b hb) body.free
  have bb := up (coherenceIsoShift b b hbb) body.free
  have iso := multiplicationCoherenceApply (x+1) (x+1) (b+1) (b+1) (r+1) 0
    (up (multiplicationCoherenceClosedShift hmul) body.free) dx dx db db
    (up (coherenceIsoShift x x hxx) body.free) bb
    (up (mulCoherenceResultShift x b r hxr) body.free) (andLeft (andRight hd))
  have result := additionCoherenceApply (r+1) 0 (b+1) (b+1) (s+1) (out+1)
    (up (additionCoherenceClosedShift hadd) body.free)
    (up (Ordinal.domainShift r hr) body.free) (andLeft hd) db db iso bb
    (up (coherenceResultShift r b s hrs) body.free) (andRight (andRight hd))
  convert result using 1 <;> (dsimp [C,body] <;> mulCoherenceWitnessSyntax)

#print axioms multiplicationCoherenceClosedShift
#print axioms multiplicationSuccessorLaw
end M6.PA.RelationalSource.PairGraph
