module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedArithmeticTransport
@[expose] public section

/-! Literal variable arithmetic values yield exact graph relations on the
supplied environment representatives, using ordinary equality only. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.addResult PairGraph.mulResult Ordinal.successor
set_option maxHeartbeats 800000

def binaryVariableValue {Γ : List Form} {n : Nat} (E : FormulaEquality Γ) (op : BinaryOperation)
    (i j : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0) (z : Term 0)
    (h : ND.Proof Γ (value (op.term (.bvar i) (.bvar j)) b f z)) :
    ND.Proof Γ (op.result (b i) (b j) z) := by
  apply binaryValueElim op (.bvar i) (.bvar j) b f z _ h
  let d : Form := binaryWitness op (.bvar i) (.bvar j) b f z
  let C := d::shifted (shifted Γ)
  have hd : ND.Proof C d := assumption (by simp [C])
  have hl := andLeft hd
  have hr := andLeft (andRight hd)
  rw [value_bvar] at hl hr
  have out := binaryInputsTransport
    (E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)) op
    (.fvar 1) (Rew.shift (Rew.shift (b i))) (.fvar 0) (Rew.shift (Rew.shift (b j)))
    (Rew.shift (Rew.shift z)) (andRight hl) (andRight hr) (andRight (andRight hd))
  convert out using 1 <;>
    (dsimp [C,d,binaryWitness,freeShiftEnv] <;> arithmeticValueSyntax)

def successorVariableValue {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (i : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0) (z : Term 0)
    (h : ND.Proof Γ (value (Presentation.succ (.bvar i)) b f z)) :
    ND.Proof Γ (Ordinal.successor (b i) z) := by
  apply successorValueElim (.bvar i) b f z _ h
  let d : Form := value (.bvar i) (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) ⋏
    Ordinal.successor (.fvar 0) (Rew.shift z)
  let C := d::shifted Γ
  have hd : ND.Proof C d := assumption (by simp [C])
  have hv := andLeft hd
  rw [value_bvar] at hv
  have out := successorInputTransport (E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp))
    (.fvar 0) (Rew.shift (b i)) (Rew.shift z) (andRight hv) (andRight hd)
  convert out using 1 <;> (dsimp [C,d,freeShiftEnv] <;> interpretedWitnessSyntax)

#print axioms binaryVariableValue
#print axioms successorVariableValue
end M6.PA.ForwardRelational
