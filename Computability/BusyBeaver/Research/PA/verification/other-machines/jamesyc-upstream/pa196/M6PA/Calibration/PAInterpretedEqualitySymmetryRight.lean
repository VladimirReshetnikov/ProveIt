module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedEqualityWitnesses
public import M6PA.Calibration.PAForwardRelationalTotalityRewriting
public import M6PA.Calibration.RelationalOrderIsoClosedSymmetry
@[expose] public section

/-! Swap actual interpreted-equality witnesses using the supplied closed
isomorphism symmetry theorem; no uniqueness of term values is needed. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 600000

def interpretedSymmetryShift {Γ : List Form}
    (h : ND.Proof Γ PairGraph.isoSymmetryClosed) : ND.Proof (shifted Γ) PairGraph.isoSymmetryClosed := by
  convert shiftProof h using 1 <;>
    ((try simp only [PairGraph.isoSymmetryClosed_eq]) <;> interpretedWitnessSyntax)

def equalityPayload {n m : Nat} (s t : SourceTerm n)
    (b : Fin n → Term m) (f : Nat → Term m) (x : Term m) : Formula m :=
  ∃¹ (value s (shiftEnv b) (shiftEnv f) (Rew.bShift x) ⋏
    (value t (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏ PairGraph.orderIso (Rew.bShift x) (.bvar 0)))

def equalitySymmetryRight {Γ : List Form} {n : Nat} (s t : SourceTerm n)
    (b : Fin n → Term 0) (f : Nat → Term 0) (x : Term 0)
    (hsym : ND.Proof Γ PairGraph.isoSymmetryClosed)
    (h : ND.Proof Γ (equalityPayload s t b f x)) : ND.Proof Γ (equal t s b f) := by
  apply exsElim h
  let body : Formula 1 := value s (shiftEnv b) (shiftEnv f) (Rew.bShift x) ⋏
    (value t (shiftEnv b) (shiftEnv f) (.bvar 0) ⋏ PairGraph.orderIso (Rew.bShift x) (.bvar 0))
  let C := body.free::shifted Γ
  let bs : Fin n → Term 0 := fun i => Rew.shift (b i)
  let fs : Nat → Term 0 := fun i => Rew.shift (f i)
  have hd : ND.Proof C (value s bs fs (Rew.shift x) ⋏
      (value t bs fs (.fvar 0) ⋏ PairGraph.orderIso (Rew.shift x) (.fvar 0))) := by
    have hh : ND.Proof C body.free := assumption (by simp [C])
    convert hh using 1 <;> (dsimp [body,bs,fs] <;> interpretedWitnessSyntax)
  have hx := valueDomain s bs fs (Rew.shift x) (andLeft hd)
  have hi : ND.Proof C (PairGraph.orderIso (.fvar 0) (Rew.shift x)) := by
    cases x with
    | bvar i => nomatch i
    | func fn _ => nomatch fn
    | fvar k =>
      exact PairGraph.isoSymmetryClosedAt (k+1) 0
        (up (interpretedSymmetryShift hsym) body.free) hx (andRight (andRight hd))
  have out := equalityValueIntro t s bs fs (.fvar 0) (Rew.shift x)
    (andLeft (andRight hd)) (andLeft hd) hi
  convert out using 1 <;> (dsimp [C,body,bs,fs] <;> interpretedWitnessSyntax)

#print axioms interpretedSymmetryShift
#print axioms equalitySymmetryRight
end M6.PA.ForwardRelational
