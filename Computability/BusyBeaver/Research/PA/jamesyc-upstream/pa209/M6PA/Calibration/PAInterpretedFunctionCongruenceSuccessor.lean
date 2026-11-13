module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedFunctionCongruenceWitnesses
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def successorVariablesEqual {Γ : List Form} {n : Nat}
    (A : CoherencePremises Γ) (T : TotalityPremises Γ)
    (i j : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (hi : ND.Proof Γ (Ordinal.domain (b i)))
    (hj : ND.Proof Γ (Ordinal.domain (b j)))
    (hij : ND.Proof Γ (PairGraph.orderIso (b i) (b j))) :
    ND.Proof Γ (equal (Presentation.succ (.bvar i)) (Presentation.succ (.bvar j)) b f) := by
  have hs := termTotality T (Presentation.succ (.bvar i)) b f (Fin.cases hi (fun a => Fin.elim0 a))
  have ht := termTotality T (Presentation.succ (.bvar j)) b f (Fin.cases hj (fun a => Fin.elim0 a))
  apply equalOfTotalValues _ _ b f hs ht
  let bs := freeShiftEnv (freeShiftEnv b)
  let fs := freeShiftEnv (freeShiftEnv f)
  let p := value (Presentation.succ (.bvar i)) (freeShiftEnv b) (freeShiftEnv f) (.fvar 0)
  let q := value (Presentation.succ (.bvar j)) bs fs (.fvar 0)
  let C := q :: shifted (p :: shifted Γ)
  let AA := (A.shift.up p).shift.up q
  have hv : ND.Proof C (value (Presentation.succ (.bvar i)) bs fs (.fvar 1)) := by
    simpa only [p,value_shift,Rew.shift_fvar] using
      up (shiftProof (assumption (Γ := p :: shifted Γ) (p := p) (by simp))) q
  have hw : ND.Proof C q := assumption (by simp [C])
  have hh : ND.Proof C (PairGraph.orderIso (bs i) (bs j)) :=
    up (isoShift (up (isoShift hij) p)) q
  let s : SourceTerm 1 := Presentation.succ (.bvar 0)
  have hv' : ND.Proof C (value s (fun _ => bs i) fs (.fvar 1)) := by
    simpa only [s,value_succ,value_bvar,shiftEnv] using hv
  have hw' : ND.Proof C (value s (fun _ => bs j) fs (.fvar 0)) := by
    simpa only [s,q,value_succ,value_bvar,shiftEnv] using hw
  exact termValuesCoherent s AA _ _ fs fs (Fin.cases hh (fun a => Fin.elim0 a)) _ _ hv' hw'

#print axioms successorVariablesEqual
end M6.PA.ForwardRelational

