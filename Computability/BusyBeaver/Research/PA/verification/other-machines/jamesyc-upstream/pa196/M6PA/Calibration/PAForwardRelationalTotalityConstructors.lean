module
public import M6PA.Theory
public import M6PA.Calibration.PAForwardRelationalTotalityOutputs
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] Ordinal.domain Ordinal.zero Ordinal.successor
  PairGraph.addResult PairGraph.mulResult value

def successorTotal {Γ : List Form} {n : Nat} (A : TotalityPremises Γ)
    (t : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (ht : ND.Proof Γ (hasValue t b f)) : ND.Proof Γ (hasValue (Presentation.succ t) b f) := by
  apply valueElim t b f _ ht
  let p := value t (freeShiftEnv b) (freeShiftEnv f) (.fvar 0)
  have hx : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  rw [hasValue_shift]
  exact successorValueFromOutput t _ _ (.fvar 0) hx
    ((A.shift.up p).successorAt (.fvar 0) (valueDomain t _ _ _ hx))

def additionTotal {Γ : List Form} {n : Nat} (A : TotalityPremises Γ)
    (s t : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (hs : ND.Proof Γ (hasValue s b f)) (ht : ND.Proof Γ (hasValue t b f)) :
    ND.Proof Γ (hasValue (Presentation.add s t) b f) := by
  apply valueElim s b f _ hs
  let p := value s (freeShiftEnv b) (freeShiftEnv f) (.fvar 0)
  have hx : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  have ht' : ND.Proof (p :: shifted Γ) (hasValue t (freeShiftEnv b) (freeShiftEnv f)) := by
    simpa only [hasValue_shift] using up (shiftProof ht) p
  rw [hasValue_shift]
  apply valueElim t _ _ _ ht'
  let q := value t (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 0)
  have hy : ND.Proof (q :: shifted (p :: shifted Γ)) q := assumption (by simp)
  have hx' : ND.Proof (q :: shifted (p :: shifted Γ))
      (value s (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 1)) := by
    simpa only [p,value_shift,Rew.shift_fvar] using up (shiftProof hx) q
  rw [hasValue_shift]
  exact additionValueFromOutput s t _ _ (.fvar 1) (.fvar 0) hx' hy
    (((A.shift.up p).shift.up q).addAt _ _
      (valueDomain s _ _ _ hx') (valueDomain t _ _ _ hy))

def multiplicationTotal {Γ : List Form} {n : Nat} (A : TotalityPremises Γ)
    (s t : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (hs : ND.Proof Γ (hasValue s b f)) (ht : ND.Proof Γ (hasValue t b f)) :
    ND.Proof Γ (hasValue (Presentation.mul s t) b f) := by
  apply valueElim s b f _ hs
  let p := value s (freeShiftEnv b) (freeShiftEnv f) (.fvar 0)
  have hx : ND.Proof (p :: shifted Γ) p := assumption (by simp)
  have ht' : ND.Proof (p :: shifted Γ) (hasValue t (freeShiftEnv b) (freeShiftEnv f)) := by
    simpa only [hasValue_shift] using up (shiftProof ht) p
  rw [hasValue_shift]
  apply valueElim t _ _ _ ht'
  let q := value t (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 0)
  have hy : ND.Proof (q :: shifted (p :: shifted Γ)) q := assumption (by simp)
  have hx' : ND.Proof (q :: shifted (p :: shifted Γ))
      (value s (freeShiftEnv (freeShiftEnv b)) (freeShiftEnv (freeShiftEnv f)) (.fvar 1)) := by
    simpa only [p,value_shift,Rew.shift_fvar] using up (shiftProof hx) q
  rw [hasValue_shift]
  exact multiplicationValueFromOutput s t _ _ (.fvar 1) (.fvar 0) hx' hy
    (((A.shift.up p).shift.up q).mulAt _ _
      (valueDomain s _ _ _ hx') (valueDomain t _ _ _ hy))

#print axioms successorTotal
#print axioms additionTotal
#print axioms multiplicationTotal
end M6.PA.ForwardRelational
