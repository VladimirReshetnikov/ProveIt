module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedFunctionCongruenceWitnesses
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def binaryVariablesEqual {Γ : List Form} {n : Nat} (op : BinaryOperation)
    (A : CoherencePremises Γ) (T : TotalityPremises Γ)
    (i j k l : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (hi : ND.Proof Γ (Ordinal.domain (b i)))
    (hj : ND.Proof Γ (Ordinal.domain (b j)))
    (hk : ND.Proof Γ (Ordinal.domain (b k)))
    (hl : ND.Proof Γ (Ordinal.domain (b l)))
    (hij : ND.Proof Γ (PairGraph.orderIso (b i) (b j)))
    (hkl : ND.Proof Γ (PairGraph.orderIso (b k) (b l))) :
    ND.Proof Γ (equal (op.term (.bvar i) (.bvar k)) (op.term (.bvar j) (.bvar l)) b f) := by
  have cov1 : EnvironmentCoverage Γ b f (op.term (.bvar i) (.bvar k)) := by
    cases op <;> exact Fin.cases hi (Fin.cases hk (fun a => Fin.elim0 a))
  have cov2 : EnvironmentCoverage Γ b f (op.term (.bvar j) (.bvar l)) := by
    cases op <;> exact Fin.cases hj (Fin.cases hl (fun a => Fin.elim0 a))
  have hs := termTotality T _ b f cov1
  have ht := termTotality T _ b f cov2
  apply equalOfTotalValues _ _ b f hs ht
  let bs := freeShiftEnv (freeShiftEnv b)
  let fs := freeShiftEnv (freeShiftEnv f)
  let p := value (op.term (.bvar i) (.bvar k)) (freeShiftEnv b) (freeShiftEnv f) (.fvar 0)
  let q := value (op.term (.bvar j) (.bvar l)) bs fs (.fvar 0)
  let C := q :: shifted (p :: shifted Γ)
  let AA := (A.shift.up p).shift.up q
  have hv : ND.Proof C (value (op.term (.bvar i) (.bvar k)) bs fs (.fvar 1)) := by
    simpa only [p,value_shift,Rew.shift_fvar] using
      up (shiftProof (assumption (Γ := p :: shifted Γ) (p := p) (by simp))) q
  have hw : ND.Proof C q := assumption (by simp [C])
  have hh : ND.Proof C (PairGraph.orderIso (bs i) (bs j)) :=
    up (isoShift (up (isoShift hij) p)) q
  have hh' : ND.Proof C (PairGraph.orderIso (bs k) (bs l)) :=
    up (isoShift (up (isoShift hkl) p)) q
  let s : SourceTerm 2 := op.term (.bvar 0) (.bvar 1)
  let u : Fin 2 → Term 0 := ![bs i, bs k]
  let v : Fin 2 → Term 0 := ![bs j, bs l]
  have hv' : ND.Proof C (value s u fs (.fvar 1)) := by
    cases op <;> simpa only [s,u,BinaryOperation.term,value_add,value_mul,value_bvar,shiftEnv,Matrix.cons_val_zero,Matrix.cons_val_one] using hv
  have hw' : ND.Proof C (value s v fs (.fvar 0)) := by
    cases op <;> simpa only [s,v,q,BinaryOperation.term,value_add,value_mul,value_bvar,shiftEnv,Matrix.cons_val_zero,Matrix.cons_val_one] using hw
  have hc : IsoCoverage C u v fs fs s := by
    cases op <;> exact Fin.cases hh (Fin.cases hh' (fun a => Fin.elim0 a))
  exact termValuesCoherent s AA u v fs fs hc _ _ hv' hw'

#print axioms binaryVariablesEqual
end M6.PA.ForwardRelational

