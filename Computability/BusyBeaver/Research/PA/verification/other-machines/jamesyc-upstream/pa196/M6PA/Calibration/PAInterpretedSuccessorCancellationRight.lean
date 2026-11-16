module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedEqualitySymmetry
public import M6PA.Calibration.RelationalOrderIsoSuccessorCancel
@[expose] public section

/-! Actual successor-value cancellation, eliminating the right child witness. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

def interpretedIsoShift {Γ : List Form} (x y : Nat)
    (h : ND.Proof Γ (PairGraph.orderIso (.fvar x) (.fvar y))) :
    ND.Proof (shifted Γ) (PairGraph.orderIso (.fvar (x+1)) (.fvar (y+1))) := by
  convert shiftProof h using 1 <;> interpretedWitnessSyntax

def successorValuesCancelRight {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (t u : SourceTerm n) (b : Fin n → Term 0) (f : Nat → Term 0) (a x y : Nat)
    (hsep : ND.Proof Γ PairGraph.closedStrictSeparation)
    (ha : ND.Proof Γ (value t b f (.fvar a)))
    (hax : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar x)))
    (hu : ND.Proof Γ (value (Presentation.succ u) b f (.fvar y)))
    (hi : ND.Proof Γ (PairGraph.orderIso (.fvar x) (.fvar y))) :
    ND.Proof Γ (equal t u b f) := by
  rw [value_succ] at hu
  have hy := andLeft hu
  apply exsElim (andRight hu)
  let body : Formula 1 := value u (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏ Ordinal.successor (.bvar 0) (.fvar y)
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun i => Rew.shift (b i)
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have hd : ND.Proof C (value u bs fs (.fvar 0) ⋏ Ordinal.successor (.fvar 0) (.fvar (y+1))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body,bs,fs] <;> interpretedWitnessSyntax)
  let EE := E.shifted.weaken (fun p hp => List.mem_cons_of_mem body.free hp)
  have low := PairGraph.orderIsoSuccessorCancel EE (x+1) (y+1) (a+1) 0
    (up (PairGraph.predecessorClosedSeparationShift hsep) body.free)
    (up (Ordinal.domainShift y hy) body.free) (up (Ordinal.successorShift a x hax) body.free)
    (andRight hd) (up (interpretedIsoShift x y hi) body.free)
  have ht : ND.Proof C (value t bs fs (.fvar (a+1))) := by
    convert up (shiftProof ha) body.free using 1 <;> (dsimp [bs,fs] <;> interpretedWitnessSyntax)
  have out := equalityValueIntro t u bs fs (.fvar (a+1)) (.fvar 0) ht (andLeft hd) low
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax)

#print axioms successorValuesCancelRight
end M6.PA.ForwardRelational
