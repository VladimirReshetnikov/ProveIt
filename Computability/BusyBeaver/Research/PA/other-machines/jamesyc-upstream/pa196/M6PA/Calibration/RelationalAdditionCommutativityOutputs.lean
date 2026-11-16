module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCommutativityLowerWitness
@[expose] public section

/-! Restrict the original left addition trace and retain its actual predecessor
output before choosing the two later existential witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def additionCommutativityOutputs {Γ : List Form} (p x y r s : Nat)
    (I : AdditionCommutativityFrame Γ p x y)
    (hxr : ND.Proof Γ (addResult (.fvar x) (.fvar y) (.fvar r)))
    (hys : ND.Proof Γ (addResult (.fvar y) (.fvar x) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  have hex := addResultPredecessor I.basis.equality p x y r I.basis.separation
    I.previousDomain I.next hxr
  apply exsElim hex
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (addResult (.fvar p) (.fvar y) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar r))
  let C := body.free::shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (addResult (.fvar (p+1)) (.fvar (y+1)) (.fvar 0) ⋏
        Ordinal.successor (.fvar 0) (.fvar (r+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> commutativityWitnessSyntax)
  let J := I.shift.weaken (fun t ht => List.mem_cons_of_mem body.free ht)
  have out := additionCommutativityLowerWitness (p+1) (x+1) (y+1) 0 (r+1) (s+1) J
    (andLeft hd) (andLeft (andRight hd)) (andRight (andRight hd))
    (up (coherenceResultShift y x s hys) body.free)
  convert out using 1 <;> (dsimp [C,body] <;> commutativityWitnessSyntax)

#print axioms additionCommutativityOutputs
end M6.PA.RelationalSource.PairGraph
