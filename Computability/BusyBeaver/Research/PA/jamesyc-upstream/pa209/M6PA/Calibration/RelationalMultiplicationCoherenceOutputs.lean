module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceOutputRight
@[expose] public section

/-! Both actual predecessor-output witnesses are retained through the successor step. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)
attribute [local irreducible] mulResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def multiplicationCoherenceOutputs {Γ : List Form} (p q b c r s : Nat)
    (I : MultiplicationCoherenceFrame Γ p q b c)
    (hr : ND.Proof Γ (mulPredecessorResult (.fvar p) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (mulPredecessorResult (.fvar q) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  apply exsElim hr
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (mulResult (.fvar p) (.fvar b) (.bvar 0) ⋏ addResult (.bvar 0) (.fvar b) (.fvar r))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (mulResult (.fvar (p+1)) (.fvar (b+1)) (.fvar 0) ⋏
        addResult (.fvar 0) (.fvar (b+1)) (.fvar (r+1)))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> mulCoherenceWitnessSyntax)
  let J := I.shift.weaken (fun t ht => List.mem_cons_of_mem body.free ht)
  have out := multiplicationCoherenceOutputRight (p+1) (q+1) (b+1) (c+1) (r+1) (s+1) 0 J
    (andLeft hd) (andLeft (andRight hd)) (andRight (andRight hd))
    (up (mulCoherencePreviousShift q c s hs) body.free)
  convert out using 1 <;> (dsimp [C,body] <;> mulCoherenceWitnessSyntax)

#print axioms multiplicationCoherenceOutputs
end M6.PA.RelationalSource.PairGraph
