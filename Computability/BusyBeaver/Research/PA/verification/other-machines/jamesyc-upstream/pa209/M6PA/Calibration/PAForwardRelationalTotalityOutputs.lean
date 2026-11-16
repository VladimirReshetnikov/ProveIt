module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalTotalityWitnesses
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult value

/-- Eliminate the arithmetic output witness, rather than select a representative. -/
def successorValueFromOutput {Γ : List Form} {n : Nat} (t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (x : Term 0)
    (hx : ND.Proof Γ (value t b f x))
    (ho : ND.Proof Γ (Ordinal.domainSuccessorExists x)) :
    ND.Proof Γ (hasValue (Presentation.succ t) b f) := by
  apply exsElim ho
  let σ : Formula 1 := Ordinal.domain (.bvar 0) ⋏ Ordinal.successor (Rew.bShift x) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hout : ND.Proof C (Ordinal.domain (.fvar 0) ⋏ Ordinal.successor (Rew.shift x) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ]; valueWitnessSyntax)
  have hxs : ND.Proof C (value t (freeShiftEnv b) (freeShiftEnv f) (Rew.shift x)) := by
    simpa only [value_shift] using up (shiftProof hx) σ.free
  rw [hasValue_shift]
  exact valueIntro _ _ _ (.fvar 0)
    (successorValueIntro t _ _ (Rew.shift x) (.fvar 0) hxs (andLeft hout) (andRight hout))

def additionValueFromOutput {Γ : List Form} {n : Nat} (s t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (x y : Term 0)
    (hx : ND.Proof Γ (value s b f x)) (hy : ND.Proof Γ (value t b f y))
    (ho : ND.Proof Γ (PairGraph.addOutput x y)) :
    ND.Proof Γ (hasValue (Presentation.add s t) b f) := by
  apply exsElim ho
  let σ : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    PairGraph.addResult (Rew.bShift x) (Rew.bShift y) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hout : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      PairGraph.addResult (Rew.shift x) (Rew.shift y) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ]; valueWitnessSyntax)
  have hxs : ND.Proof C (value s (freeShiftEnv b) (freeShiftEnv f) (Rew.shift x)) := by
    simpa only [value_shift] using up (shiftProof hx) σ.free
  have hys : ND.Proof C (value t (freeShiftEnv b) (freeShiftEnv f) (Rew.shift y)) := by
    simpa only [value_shift] using up (shiftProof hy) σ.free
  rw [hasValue_shift]
  exact valueIntro _ _ _ (.fvar 0)
    (additionValueIntro s t _ _ (Rew.shift x) (Rew.shift y) (.fvar 0)
      hxs hys (andLeft hout) (andRight hout))

def multiplicationValueFromOutput {Γ : List Form} {n : Nat} (s t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (x y : Term 0)
    (hx : ND.Proof Γ (value s b f x)) (hy : ND.Proof Γ (value t b f y))
    (ho : ND.Proof Γ (PairGraph.mulOutput x y)) :
    ND.Proof Γ (hasValue (Presentation.mul s t) b f) := by
  apply exsElim ho
  let σ : Formula 1 := Ordinal.domain (.bvar 0) ⋏
    PairGraph.mulResult (Rew.bShift x) (Rew.bShift y) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hout : ND.Proof C (Ordinal.domain (.fvar 0) ⋏
      PairGraph.mulResult (Rew.shift x) (Rew.shift y) (.fvar 0)) := by
    have hh : ND.Proof C σ.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [σ]; valueWitnessSyntax)
  have hxs : ND.Proof C (value s (freeShiftEnv b) (freeShiftEnv f) (Rew.shift x)) := by
    simpa only [value_shift] using up (shiftProof hx) σ.free
  have hys : ND.Proof C (value t (freeShiftEnv b) (freeShiftEnv f) (Rew.shift y)) := by
    simpa only [value_shift] using up (shiftProof hy) σ.free
  rw [hasValue_shift]
  exact valueIntro _ _ _ (.fvar 0)
    (multiplicationValueIntro s t _ _ (Rew.shift x) (Rew.shift y) (.fvar 0)
      hxs hys (andLeft hout) (andRight hout))

#print axioms successorValueFromOutput
#print axioms additionValueFromOutput
#print axioms multiplicationValueFromOutput
end M6.PA.ForwardRelational
