import BusyBeaver.ZFC.ArithmeticCantor

set_option autoImplicit false

/-!
# The nine-register file and live control states (catalogue independent)

The coded register file, its projections and one-field writes, the opcode
effect, and the live state `liveValue control file = P(control,file)+1`, exactly
as in the Codex lane's `ArithmeticControlStep254`, without its Prog254 control
tables. Having them separately keeps catalogue-generic interpreters (and their
import closures) free of the Prog254 decoder-coverage certificate.

The definitions and proofs are copied from `ArithmeticControlStep254`
(Codex lane); the two copies are definitionally identical.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlFile
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

section Tuple
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- An externally fixed arity, not a model-coded list. The last field is the
remaining tail itself, making this a bijection on all arithmetic codes. -/
noncomputable def tupleValue : (n : Nat) → (Fin (n+1) → V) → V
  | 0, values => values 0
  | n+1, values => cantor (values 0) (tupleValue n (fun i => values i.succ))

noncomputable def tupleProjection : (n : Nat) → V → Fin (n+1) → V
  | 0, code, _ => code
  | n+1, code, i => Fin.cases (first code) (fun j => tupleProjection n (second code) j) i

theorem tupleProjection_value (n : Nat) (values : Fin (n+1) → V) :
    tupleProjection n (tupleValue n values) = values := by
  induction n with
  | zero => funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [tupleProjection,tupleValue,Fin.cases_zero,first_cantor]
      · simpa only [tupleProjection,tupleValue,Fin.cases_succ,second_cantor] using
          congrFun (ih (fun j => values j.succ)) j

theorem tupleValue_projection (n : Nat) (code : V) :
    tupleValue n (tupleProjection n code) = code := by
  induction n generalizing code with
  | zero => rfl
  | succ n ih =>
      simpa only [tupleValue,tupleProjection,Fin.cases_zero,Fin.cases_succ,ih]
        using cantor_projections code

def projectionDef : (n : Nat) → Fin (n+1) → 𝚺₁.Semisentence 2
  | 0, _ => .mkSigma “out code. out = code”
  | n+1, i => Fin.cases
      (.mkSigma “out code. !ArithmeticCantor.firstDef out code”)
      (fun j => .mkSigma
        “out code. ∃ tail, !ArithmeticCantor.secondDef tail code ∧
          !(projectionDef n j) out tail”) i

instance projection_defined (n : Nat) (i : Fin (n+1)) :
    𝚺₁-Function₁[V] (fun code => tupleProjection n code i) via projectionDef n i := by
  induction n with
  | zero => exact .mk fun e => by simp [projectionDef,tupleProjection]
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact .mk fun e => by simp [projectionDef,tupleProjection]
      · exact .mk fun e => by simp [projectionDef,tupleProjection,(ih j).iff]

/-- Nine fields use eight pairs; register8 is the unpaired final tail. -/
noncomputable def fileValue (values : Fin 9 → V) : V := tupleValue 8 values
noncomputable def regValue (code : V) (i : Fin 9) : V := tupleProjection 8 code i

def fileDef : 𝚺₁.Semisentence 10 := .mkSigma
  “out v0 v1 v2 v3 v4 v5 v6 v7 v8.
    ∃ p7, !ArithmeticCantor.pairDef p7 v7 v8 ∧
    ∃ p6, !ArithmeticCantor.pairDef p6 v6 p7 ∧
    ∃ p5, !ArithmeticCantor.pairDef p5 v5 p6 ∧
    ∃ p4, !ArithmeticCantor.pairDef p4 v4 p5 ∧
    ∃ p3, !ArithmeticCantor.pairDef p3 v3 p4 ∧
    ∃ p2, !ArithmeticCantor.pairDef p2 v2 p3 ∧
    ∃ p1, !ArithmeticCantor.pairDef p1 v1 p2 ∧
    !ArithmeticCantor.pairDef out v0 p1”

instance file_defined : HierarchySymbol.DefinedFunction (V := V)
    (fun values : Fin 9 → V => fileValue values) fileDef :=
  .mk fun e => by simp [fileDef,fileValue,tupleValue]

@[simp] theorem reg_file (values : Fin 9 → V) (i : Fin 9) :
    regValue (fileValue values) i = values i := congrFun (tupleProjection_value 8 values) i
@[simp] theorem file_reg (code : V) : fileValue (regValue code) = code :=
  tupleValue_projection 8 code

/-- Fixed finite selector. Every out-of-range internal selector returns zero. -/
noncomputable def selectFrom : List (Fin 9) → V → V → V
  | [], _, _ => 0
  | i::indices, code, index =>
      if index = (i.val : V) then regValue code i else selectFrom indices code index

def selectFromDef : List (Fin 9) → 𝚺₁.Semisentence 3
  | [] => .mkSigma “out code index. out = 0”
  | i::indices => .mkSigma
      “out code index.
        ((index = !!(Semiterm.Operator.numeral ℒₒᵣ i.val)) ∧
          !(projectionDef 8 i) out code) ∨
        ((index ≠ !!(Semiterm.Operator.numeral ℒₒᵣ i.val)) ∧
          !(selectFromDef indices) out code index)”

instance selectFrom_defined (indices : List (Fin 9)) :
    𝚺₁-Function₂[V] (selectFrom indices) via selectFromDef indices := by
  induction indices with
  | nil => exact .mk fun e => by simp [selectFromDef,selectFrom]
  | cons i indices ih =>
      refine .mk fun e => ?_
      classical
      by_cases h : e 2 = (i.val : V) <;>
        simp [selectFromDef,selectFrom,regValue,numeral_eq_natCast,h,ih.iff,
          (projection_defined 8 i).iff]

theorem selectFrom_at (indices : List (Fin 9)) (i : Fin 9) (hi : i ∈ indices) (code : V) :
    selectFrom indices code (i.val : V) = regValue code i := by
  induction indices with
  | nil => simp at hi
  | cons j indices ih =>
      classical
      by_cases he : j=i
      · subst j; simp only [selectFrom,if_true]
      · have hcast : (i.val : V) ≠ (j.val : V) := by
          intro h
          exact he (Fin.ext (by simpa only [Nat.cast_inj] using h.symm))
        have ht : i ∈ indices := by
          rcases List.mem_cons.mp hi with hh | ht
          · exact False.elim (he hh.symm)
          · exact ht
        simpa only [selectFrom,if_neg hcast] using ih ht

noncomputable def selectedValue (code index : V) : V := selectFrom (List.finRange 9) code index
def selectedDef : 𝚺₁.Semisentence 3 := selectFromDef (List.finRange 9)
instance selected_defined : 𝚺₁-Function₂[V] selectedValue via selectedDef :=
  selectFrom_defined _

theorem selected_at (code : V) (i : Fin 9) :
    selectedValue code (i.val : V) = regValue code i := selectFrom_at _ i (by simp) code

/-- A fixed-index update test preserves all other physical fields. -/
noncomputable def writeFieldValue (i : Fin 9) (index value code : V) : V :=
  if index = (i.val : V) then value else regValue code i

def writeFieldDef (i : Fin 9) : 𝚺₁.Semisentence 4 := .mkSigma
  “out index value code.
    ((index = !!(Semiterm.Operator.numeral ℒₒᵣ i.val)) ∧ out = value) ∨
    ((index ≠ !!(Semiterm.Operator.numeral ℒₒᵣ i.val)) ∧ !(projectionDef 8 i) out code)”

instance writeField_defined (i : Fin 9) :
    𝚺₁-Function₃[V] (writeFieldValue i) via writeFieldDef i := .mk fun e => by
  classical
  by_cases h : e 1 = (i.val : V) <;>
    simp [writeFieldDef,writeFieldValue,regValue,numeral_eq_natCast,h,
      (projection_defined 8 i).iff]

noncomputable def writeValue (index value code : V) : V :=
  fileValue (fun i => writeFieldValue i index value code)

def writeDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out index value code.
    ∃ v0, !(writeFieldDef 0) v0 index value code ∧
    ∃ v1, !(writeFieldDef 1) v1 index value code ∧
    ∃ v2, !(writeFieldDef 2) v2 index value code ∧
    ∃ v3, !(writeFieldDef 3) v3 index value code ∧
    ∃ v4, !(writeFieldDef 4) v4 index value code ∧
    ∃ v5, !(writeFieldDef 5) v5 index value code ∧
    ∃ v6, !(writeFieldDef 6) v6 index value code ∧
    ∃ v7, !(writeFieldDef 7) v7 index value code ∧
    ∃ v8, !(writeFieldDef 8) v8 index value code ∧
    !fileDef out v0 v1 v2 v3 v4 v5 v6 v7 v8”
instance write_defined : 𝚺₁-Function₃[V] writeValue via writeDef := .mk fun e => by
  simp [writeDef,writeValue,fileValue,tupleValue]

@[simp] theorem reg_write (index value code : V) (i : Fin 9) :
    regValue (writeValue index value code) i =
      if index = (i.val : V) then value else regValue code i := by
  rw [writeValue,reg_file]
  rfl

theorem write_at (code value : V) (i : Fin 9) :
    regValue (writeValue (i.val : V) value code) i = value := by simp

theorem write_other (code value : V) (i j : Fin 9) (h : i ≠ j) :
    regValue (writeValue (i.val : V) value code) j = regValue code j := by
  have hn : (i.val : V) ≠ (j.val : V) := by
    intro he; exact h (Fin.ext (by simpa only [Nat.cast_inj] using he))
  simp [hn]

noncomputable def effectValue (opcode index code : V) : V :=
  if opcode = 1 then writeValue index (selectedValue code index+1) code
  else if opcode = 2 then writeValue index (selectedValue code index-1) code
  else code

def effectDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out opcode index code. ∃ selected, !selectedDef selected code index ∧
    ((opcode = 1 ∧ !writeDef out index (selected+1) code) ∨
     (opcode ≠ 1 ∧ opcode = 2 ∧ ∃ pred, !subDef pred selected 1 ∧
       !writeDef out index pred code) ∨
     (opcode ≠ 1 ∧ opcode ≠ 2 ∧ out = code))”
instance effect_defined : 𝚺₁-Function₃[V] effectValue via effectDef := .mk fun e => by
  classical
  by_cases h1 : e 1 = 1
  · simp [effectDef,effectValue,h1]
  · by_cases h2 : e 1 = 2 <;> simp [effectDef,effectValue,h1,h2]

end Tuple

section Live
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

/-- Every positive live code is decoded via its predecessor. In particular,
code1 encodes control0/file0 and is positive, although control0 is invalid.
It is not absorbing halt0. -/
noncomputable def liveValue (control file : V) : V := cantor control file + 1

def liveDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out control file. ∃ pair, !ArithmeticCantor.pairDef pair control file ∧ out = pair+1”
instance live_defined : 𝚺₁-Function₂[V] liveValue via liveDef :=
  .mk fun e => by simp [liveDef,liveValue]

noncomputable def controlValue (state : V) : V := first (state-1)
noncomputable def fileCodeValue (state : V) : V := second (state-1)

def controlDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out state. ∃ pred, !subDef pred state 1 ∧ !ArithmeticCantor.firstDef out pred”
def fileCodeDef : 𝚺₁.Semisentence 2 := .mkSigma
  “out state. ∃ pred, !subDef pred state 1 ∧ !ArithmeticCantor.secondDef out pred”
instance control_defined : 𝚺₁-Function₁[V] controlValue via controlDef :=
  .mk fun e => by simp [controlDef,controlValue]
instance fileCode_defined : 𝚺₁-Function₁[V] fileCodeValue via fileCodeDef :=
  .mk fun e => by simp [fileCodeDef,fileCodeValue]

@[simp] theorem live_ne_zero (q file : V) : liveValue q file ≠ 0 := by simp [liveValue]
@[simp] theorem control_live (q file : V) : controlValue (liveValue q file) = q := by
  simp [controlValue,liveValue]
@[simp] theorem fileCode_live (q file : V) : fileCodeValue (liveValue q file) = file := by
  simp [fileCodeValue,liveValue]

theorem live_decode (state : V) (hs : state ≠ 0) :
    liveValue (controlValue state) (fileCodeValue state) = state := by
  simp only [liveValue,controlValue,fileCodeValue,cantor_projections]
  have hpos : 0 < state := lt_of_le_of_ne (Arithmetic.zero_le state) (Ne.symm hs)
  exact tsub_add_cancel_of_le (by simpa using lt_iff_succ_le.mp hpos)

end Live
end SetTheory.BusyBeaver.ZFC.ArithmeticControlFile
