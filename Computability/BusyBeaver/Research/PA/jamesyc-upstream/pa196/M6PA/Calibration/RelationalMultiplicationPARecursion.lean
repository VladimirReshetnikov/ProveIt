module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCommutativityApplications
public import M6PA.Calibration.RelationalMultiplicationSuccessorLaw
@[expose] public section

/-! Match the literal PAeq multiplication recursion orientation: the added base
is on the left. The actual graph's opposite addition orientation is reconciled
by the proved commutativity theorem, not by altering either definition. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult mulResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def multiplicationPARecursion {Γ : List Form} (E : FormulaEquality Γ)
    (x u b r t out : Nat)
    (hsep : ND.Proof Γ closedInclusiveSeparation)
    (hidentity : ND.Proof Γ identityStatement)
    (hadd : ND.Proof Γ addCoherenceStatement)
    (hmul : ND.Proof Γ mulCoherenceStatement)
    (hcomm : ND.Proof Γ addCommutativityStatement)
    (htrans : ND.Proof Γ isoTransitivityClosed)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hr : ND.Proof Γ (Ordinal.domain (.fvar r)))
    (ht : ND.Proof Γ (Ordinal.domain (.fvar t)))
    (hxu : ND.Proof Γ (Ordinal.successor (.fvar x) (.fvar u)))
    (hxr : ND.Proof Γ (mulResult (.fvar x) (.fvar b) (.fvar r)))
    (hbt : ND.Proof Γ (addResult (.fvar b) (.fvar r) (.fvar t)))
    (huo : ND.Proof Γ (mulResult (.fvar u) (.fvar b) (.fvar out)))
    (houtput : ND.Proof Γ (addOutput (.fvar r) (.fvar b))) :
    ND.Proof Γ (orderIso (.fvar t) (.fvar out)) := by
  apply exsElim houtput
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏ addResult (.fvar r) (.fvar b) (.bvar 0)
  let C := body.free::shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏ addResult (.fvar (r+1)) (.fvar (b+1)) (.fvar 0)) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> commutativityWitnessSyntax)
  let EE := E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp)
  have left := additionCommutativityApply (b+1) (r+1) (t+1) 0
    (up (additionCommutativityClosedShift hcomm) body.free)
    (up (Ordinal.domainShift b hb) body.free) (up (Ordinal.domainShift r hr) body.free)
    (up (coherenceResultShift b r t hbt) body.free) (andRight hd)
  have right := multiplicationSuccessorLaw EE (x+1) (u+1) (b+1) (r+1) 0 (out+1)
    (up (additionInclusiveSeparationShift hsep) body.free)
    (up (rightSuccessorIdentityShift hidentity) body.free)
    (up (additionCoherenceClosedShift hadd) body.free)
    (up (multiplicationCoherenceClosedShift hmul) body.free)
    (up (Ordinal.domainShift x hx) body.free) (up (Ordinal.domainShift b hb) body.free)
    (up (Ordinal.domainShift r hr) body.free) (up (Ordinal.successorShift x u hxu) body.free)
    (up (mulCoherenceResultShift x b r hxr) body.free) (andRight hd)
    (up (mulCoherenceResultShift u b out huo) body.free)
  have hs : ND.Proof (shifted Γ) isoTransitivityClosed := by
    convert shiftProof htrans using 1 <;>
      ((try simp only [isoTransitivityClosed_eq]) <;> addCommutativitySyntax)
  have result := isoTransitivityClosedAt (t+1) 0 (out+1) (up hs body.free)
    (up (Ordinal.domainShift t ht) body.free) left right
  convert result using 1 <;> (dsimp [C,body] <;> mulCoherenceWitnessSyntax)

#print axioms multiplicationPARecursion
end M6.PA.RelationalSource.PairGraph
