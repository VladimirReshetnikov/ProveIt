module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceFrame
public import M6PA.Calibration.RelationalAdditionCoherenceOutputRight
@[expose] public section

/-! The first-argument additive recursion equation modulo witnessed isomorphism.
Two arbitrary actual traces are compared; no choice of arithmetic graph is fixed. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 600000

def additionSuccessorLaw {Γ : List Form} (E : FormulaEquality Γ)
    (x u b r v w : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hsep : ND.Proof Γ closedInclusiveSeparation)
    (hidentity : ND.Proof Γ identityStatement)
    (hcoherence : ND.Proof Γ addCoherenceStatement)
    (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hr : ND.Proof Γ (Ordinal.domain (.fvar r)))
    (hxu : ND.Proof Γ (Ordinal.successor (.fvar x) (.fvar u)))
    (hrv : ND.Proof Γ (Ordinal.successor (.fvar r) (.fvar v)))
    (hxr : ND.Proof Γ (addResult (.fvar x) (.fvar b) (.fvar r)))
    (huw : ND.Proof Γ (addResult (.fvar u) (.fvar b) (.fvar w))) :
    ND.Proof Γ (orderIso (.fvar v) (.fvar w)) := by
  have hxx := orderIsoFromExists E x (identityAt x hidentity hx)
  have hbb := orderIsoFromExists E b (identityAt b hidentity hb)
  apply exsElim (addResultPredecessor E x u b w hsep hx hxu huw)
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (addResult (.fvar x) (.fvar b) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar w))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (addResult (.fvar (x+1)) (.fvar (b+1)) (.fvar 0) ⋏
        Ordinal.successor (.fvar 0) (.fvar (w+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> coherenceWitnessSyntax)
  let EE := E.shifted.weaken (fun t ht => List.mem_cons_of_mem body.free ht)
  have dx := up (Ordinal.domainShift x hx) body.free
  have db := up (Ordinal.domainShift b hb) body.free
  have iso := additionCoherenceApply (x+1) (x+1) (b+1) (b+1) (r+1) 0
    (up (additionCoherenceClosedShift hcoherence) body.free) dx dx db db
    (up (coherenceIsoShift x x hxx) body.free) (up (coherenceIsoShift b b hbb) body.free)
    (up (coherenceResultShift x b r hxr) body.free) (andLeft (andRight hd))
  have out := orderIsoSuccessor EE (r+1) 0 (v+1) (w+1)
    (up (emptyClosedShift hempty) body.free) (up (adjunctionClosedShift hadj) body.free)
    (up (Ordinal.domainShift r hr) body.free) (andLeft hd)
    (up (Ordinal.successorShift r v hrv) body.free) (andRight (andRight hd)) iso
  convert out using 1 <;> (dsimp [C,body] <;> coherenceWitnessSyntax)

#print axioms additionSuccessorLaw
end M6.PA.RelationalSource.PairGraph
