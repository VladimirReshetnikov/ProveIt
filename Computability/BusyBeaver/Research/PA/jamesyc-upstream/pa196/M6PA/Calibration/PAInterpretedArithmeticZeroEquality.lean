module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedArithmeticZeroValues
public import M6PA.Calibration.PAInterpretedFunctionCongruenceWitnesses
public import M6PA.Calibration.RelationalAdditionRightSuccessor
@[expose] public section

namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value equal PairGraph.orderIso Ordinal.domain
set_option maxHeartbeats 800000

def arithmeticZeroRight {n : Nat} (op : BinaryOperation) (i : Fin n) : SourceTerm n :=
  match op with
  | .addition => .bvar i
  | .multiplication => Presentation.zero

def arithmeticZeroValueIso {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (hid : ND.Proof Γ PairGraph.identityStatement)
    (op : BinaryOperation) (i : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0) (l r : Term 0)
    (hl : ND.Proof Γ (value (op.term Presentation.zero (.bvar i)) b f l))
    (hr : ND.Proof Γ (value (arithmeticZeroRight op i) b f r)) :
    ND.Proof Γ (PairGraph.orderIso l r) := by
  obtain ⟨ln,rfl⟩ := groundName l
  obtain ⟨rn,rfl⟩ := groundName r
  cases op with
  | addition =>
    have he := arithmeticZeroAddValue E i b f (.fvar ln) hl
    have hv : ND.Proof Γ (Ordinal.domain (.fvar rn) ⋏ ND.eq (.fvar rn) (b i)) := by simpa only [arithmeticZeroRight,value_bvar] using hr
    exact PairGraph.orderIsoFromEquality E ln rn hid (valueDomain _ _ _ _ hl)
      (E.transitivityOf he (E.symmetryOf (andRight hv)))
  | multiplication =>
    have hz := arithmeticZeroMulValue E i b f (.fvar ln) hl
    have hv : ND.Proof Γ (Ordinal.domain (.fvar rn) ⋏ Ordinal.zero (.fvar rn)) := by simpa only [arithmeticZeroRight,value_zero] using hr
    exact PairGraph.zeroOrderIso E ln rn hz (andRight hv)

def arithmeticZeroVariablesEqual {Γ : List Form} {n : Nat}
    (E : FormulaEquality Γ) (hid : ND.Proof Γ PairGraph.identityStatement)
    (T : TotalityPremises Γ) (op : BinaryOperation)
    (i : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0)
    (hi : ND.Proof Γ (Ordinal.domain (b i))) :
    ND.Proof Γ (equal (op.term Presentation.zero (.bvar i)) (arithmeticZeroRight op i) b f) := by
  have cl : EnvironmentCoverage Γ b f (op.term Presentation.zero (.bvar i)) := by
    cases op <;> exact Fin.cases (fun a => Fin.elim0 a) (Fin.cases hi (fun a => Fin.elim0 a))
  have cr : EnvironmentCoverage Γ b f (arithmeticZeroRight op i) := by
    cases op
    · exact hi
    · exact fun a => Fin.elim0 a
  have hs := termTotality T _ b f cl
  have ht := termTotality T _ b f cr
  apply equalOfTotalValues _ _ b f hs ht
  let bs := freeShiftEnv (freeShiftEnv b)
  let fs := freeShiftEnv (freeShiftEnv f)
  let p := value (op.term Presentation.zero (.bvar i)) (freeShiftEnv b) (freeShiftEnv f) (.fvar 0)
  let q := value (arithmeticZeroRight op i) bs fs (.fvar 0)
  let C := q::shifted (p::shifted Γ)
  have hv : ND.Proof C (value (op.term Presentation.zero (.bvar i)) bs fs (.fvar 1)) := by
    simpa only [p,value_shift,Rew.shift_fvar] using
      up (shiftProof (assumption (Γ := p::shifted Γ) (p := p) (by simp))) q
  have hw : ND.Proof C q := assumption (by simp [C])
  let EE := (E.shifted.weaken (fun a h => List.mem_cons_of_mem p h)).shifted.weaken
    (fun a h => List.mem_cons_of_mem q h)
  have id' : ND.Proof C PairGraph.identityStatement :=
    up (PairGraph.rightSuccessorIdentityShift (up (PairGraph.rightSuccessorIdentityShift hid) p)) q
  exact arithmeticZeroValueIso EE id' op i bs fs (.fvar 1) (.fvar 0) hv hw

#print axioms arithmeticZeroValueIso
#print axioms arithmeticZeroVariablesEqual
end M6.PA.ForwardRelational
