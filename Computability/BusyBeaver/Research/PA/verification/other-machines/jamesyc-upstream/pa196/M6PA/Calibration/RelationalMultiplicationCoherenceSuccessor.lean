module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceOutputs
public import M6PA.Calibration.RelationalOrderIsoSuccessorMatch
@[expose] public section

/-! Pointwise successor case of addition coherence. The matching predecessor
and both lower arithmetic outputs are actual existential witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Formula)
attribute [local irreducible] mulResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def multiplicationSuccessorCoherence {Γ : List Form} (E : FormulaEquality Γ)
    (p x y b c r s : Nat)
    (haddition : ND.Proof Γ addCoherenceStatement)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hstrict : ND.Proof Γ closedStrictSeparation)
    (hinclusive : ND.Proof Γ closedInclusiveSeparation)
    (hp : ND.Proof Γ (Ordinal.domain (.fvar p)))
    (hy : ND.Proof Γ (Ordinal.domain (.fvar y)))
    (hb : ND.Proof Γ (Ordinal.domain (.fvar b)))
    (hc : ND.Proof Γ (Ordinal.domain (.fvar c)))
    (hsucc : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar x)))
    (hih : ND.Proof Γ (mulCoherence (.fvar p)))
    (hxy : ND.Proof Γ (orderIso (.fvar x) (.fvar y)))
    (hbc : ND.Proof Γ (orderIso (.fvar b) (.fvar c)))
    (hr : ND.Proof Γ (mulResult (.fvar x) (.fvar b) (.fvar r)))
    (hs : ND.Proof Γ (mulResult (.fvar y) (.fvar c) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  apply exsElim (orderIsoSuccessorMatch E x y p hstrict hy hsucc hxy)
  let body : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    (Ordinal.successor (.bvar 0) (.fvar y) ⋏ orderIso (.fvar p) (.bvar 0))
  let C := body.free :: shifted Γ
  have hd : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      (Ordinal.successor (.fvar 0) (.fvar (y+1)) ⋏ orderIso (.fvar (p+1)) (.fvar 0))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body] <;> mulCoherenceWitnessSyntax)
  let EE := E.shifted.weaken (fun t ht => List.mem_cons_of_mem body.free ht)
  have sep := up (additionInclusiveSeparationShift hinclusive) body.free
  let I : MultiplicationCoherenceFrame C (p+1) 0 (b+1) (c+1) :=
    ⟨up (additionCoherenceClosedShift haddition) body.free,EE,up (emptyClosedShift hempty) body.free,up (adjunctionClosedShift hadj) body.free,
      up (mulCoherenceShift p hih) body.free,andLeft hd,
      up (Ordinal.domainShift b hb) body.free,up (Ordinal.domainShift c hc) body.free,
      andRight (andRight hd),up (mulCoherenceIsoShift b c hbc) body.free⟩
  have leftPrevious := mulResultPredecessor EE (p+1) (x+1) (b+1) (r+1) sep
    (up (Ordinal.domainShift p hp) body.free) (up (Ordinal.successorShift p x hsucc) body.free)
    (up (mulCoherenceResultShift x b r hr) body.free)
  have rightPrevious := mulResultPredecessor EE 0 (y+1) (c+1) (s+1) sep
    (andLeft hd) (andLeft (andRight hd)) (up (mulCoherenceResultShift y c s hs) body.free)
  have out := multiplicationCoherenceOutputs (p+1) 0 (b+1) (c+1) (r+1) (s+1) I leftPrevious rightPrevious
  convert out using 1 <;> (dsimp [C,body] <;> mulCoherenceWitnessSyntax)

#print axioms multiplicationSuccessorCoherence
end M6.PA.RelationalSource.PairGraph
