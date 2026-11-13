module
public import M6PA.Theory
public import M6PA.Calibration.PAInterpretedArithmeticVariableValues
@[expose] public section

/-! Exact graph payloads extracted from both literal sides of the PAeq
addition-successor equation, retaining the actual intermediate ordinals. -/
namespace M6.PA.ForwardRelational
open FFL FFL.FirstOrder RelationalSource ND
open Ordinal (Term Formula)
attribute [local irreducible] value PairGraph.addResult Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def additionSuccessorLeft (x b z : Term n) : Formula n :=
  ∃¹ (Ordinal.domain (.bvar 0) ⋏ (Ordinal.successor (Rew.bShift x) (.bvar 0) ⋏
    PairGraph.addResult (.bvar 0) (Rew.bShift b) (Rew.bShift z)))
def additionSuccessorRight (x b z : Term n) : Formula n :=
  ∃¹ (Ordinal.domain (.bvar 0) ⋏ (PairGraph.addResult (Rew.bShift x) (Rew.bShift b) (.bvar 0) ⋏
    Ordinal.successor (.bvar 0) (Rew.bShift z)))

macro "additionValuePayloadSyntax" : tactic => `(tactic|
  ((try simp only [additionSuccessorLeft,additionSuccessorRight,BinaryOperation.result]) <;> valueWitnessSyntax))

def additionSuccessorLeftValue {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (i j : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0) (z : Term 0)
    (h : ND.Proof Γ (value (Presentation.add (Presentation.succ (.bvar i)) (.bvar j)) b f z)) :
    ND.Proof Γ (additionSuccessorLeft (b i) (b j) z) := by
  apply binaryValueElim .addition (Presentation.succ (.bvar i)) (.bvar j) b f z _ h
  let d : Form := binaryWitness .addition (Presentation.succ (.bvar i)) (.bvar j) b f z
  let C := d::shifted (shifted Γ)
  let bs := freeShiftEnv (freeShiftEnv b)
  let fs := freeShiftEnv (freeShiftEnv f)
  let EE := E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hd : ND.Proof C d := assumption (by simp [C])
  have hy := andLeft (andRight hd)
  rw [value_bvar] at hy
  have hs := successorVariableValue EE i bs fs (.fvar 1) (andLeft hd)
  have hr := binaryInputsTransport EE .addition (.fvar 1) (.fvar 1) (.fvar 0) (bs j)
    (Rew.shift (Rew.shift z)) (EE.reflexive (.fvar 1)) (andRight hy) (andRight (andRight hd))
  apply exsIntro _ (.fvar 1)
  have out := andIntro (valueDomain _ bs fs (.fvar 1) (andLeft hd)) (andIntro hs hr)
  convert out using 1 <;>
    (dsimp [C,d,bs,fs,binaryWitness,freeShiftEnv] <;> additionValuePayloadSyntax)

def additionSuccessorRightValue {Γ : List Form} {n : Nat} (E : FormulaEquality Γ)
    (i j : Fin n) (b : Fin n → Term 0) (f : Nat → Term 0) (z : Term 0)
    (h : ND.Proof Γ (value (Presentation.succ (Presentation.add (.bvar i) (.bvar j))) b f z)) :
    ND.Proof Γ (additionSuccessorRight (b i) (b j) z) := by
  apply successorValueElim (Presentation.add (.bvar i) (.bvar j)) b f z _ h
  let d : Form := value (Presentation.add (.bvar i) (.bvar j)) (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) ⋏
    Ordinal.successor (.fvar 0) (Rew.shift z)
  let C := d::shifted Γ
  have hd : ND.Proof C d := assumption (by simp [C])
  let EE := E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have hr := binaryVariableValue EE .addition i j (freeShiftEnv b) (freeShiftEnv f) (.fvar 0) (andLeft hd)
  apply exsIntro _ (.fvar 0)
  have out := andIntro (valueDomain _ _ _ (.fvar 0) (andLeft hd)) (andIntro hr (andRight hd))
  convert out using 1 <;> (dsimp [C,d,freeShiftEnv] <;> additionValuePayloadSyntax)

#print axioms additionSuccessorLeftValue
#print axioms additionSuccessorRightValue
end M6.PA.ForwardRelational
