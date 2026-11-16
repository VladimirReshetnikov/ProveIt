module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCommutativitySuccessorWitness
@[expose] public section

/-! Obtain a reversed lower-sum witness by the fully supplied addition totality. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def additionCommutativityLowerWitness {Γ : List Form} (p x y a r s : Nat)
    (I : AdditionCommutativityFrame Γ p x y)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hpa : ND.Proof Γ (addResult (.fvar p) (.fvar y) (.fvar a)))
    (har : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar r)))
    (hys : ND.Proof Γ (addResult (.fvar y) (.fvar x) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  have hex := I.basis.addAt y p I.baseDomain I.previousDomain
  apply exsElim hex
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏ addResult (.fvar y) (.fvar p) (.bvar 0)
  let C := body.free::shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏ addResult (.fvar (y+1)) (.fvar (p+1)) (.fvar 0)) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> commutativityWitnessSyntax)
  let J := I.shift.weaken (fun t ht => List.mem_cons_of_mem body.free ht)
  have out := additionCommutativitySuccessorWitness (p+1) (x+1) (y+1) (a+1) 0 (r+1) (s+1) J
    (up (Ordinal.domainShift a ha) body.free) (andLeft hd)
    (up (coherenceResultShift p y a hpa) body.free) (andRight hd)
    (up (Ordinal.successorShift a r har) body.free)
    (up (coherenceResultShift y x s hys) body.free)
  convert out using 1 <;> (dsimp [C,body] <;> commutativityWitnessSyntax)

#print axioms additionCommutativityLowerWitness
end M6.PA.RelationalSource.PairGraph
