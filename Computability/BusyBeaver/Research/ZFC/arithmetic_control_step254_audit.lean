import BusyBeaver.ZFC.ArithmeticControlStep254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlStep254 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.tupleProjection_value
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.tupleValue_projection
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.projection_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.file_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.reg_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.file_reg
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.selectFrom_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.selectFrom_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.selected_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.write_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.reg_write
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.write_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.effect_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.registerKey_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.next_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.live_decode
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.transition_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.step_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.step_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.step_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.step_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.step_live
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.transition_invalid
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.transition_halt
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.transition_inc
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.transition_decnz
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlStep254.transition_noop

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (n : Nat) (values : Fin (n+1) → V) :
    tupleProjection n (tupleValue n values) = values := tupleProjection_value n values
example (n : Nat) (code : V) : tupleValue n (tupleProjection n code) = code :=
  tupleValue_projection n code
example (n : Nat) (i : Fin (n+1)) (out code : V) :
    (projectionDef n i).val.Evalb ![out,code] ↔ out=tupleProjection n code i := by simp
example (values : Fin 9 → V) (out : V) :
    fileDef.val.Evalb (Fin.cases out values) ↔ out=fileValue values := by simp
example (values : Fin 9 → V) (i : Fin 9) : regValue (fileValue values) i = values i :=
  reg_file values i
example (code : V) : fileValue (regValue code) = code := file_reg code
example (indices : List (Fin 9)) (out code index : V) :
    (selectFromDef indices).val.Evalb ![out,code,index] ↔
      out=selectFrom indices code index := by simp
example (indices : List (Fin 9)) (i : Fin 9) (hi : i ∈ indices) (code : V) :
    selectFrom indices code (i.val : V) = regValue code i := selectFrom_at indices i hi code
example (code : V) (i : Fin 9) : selectedValue code (i.val : V) = regValue code i := selected_at code i
example (out index value code : V) : writeDef.val.Evalb ![out,index,value,code] ↔
    out=writeValue index value code := by simp
example (index value code : V) (i : Fin 9) : regValue (writeValue index value code) i =
    if index=(i.val : V) then value else regValue code i := reg_write index value code i
example (value code : V) (i j : Fin 9) (h : i≠j) :
    regValue (writeValue (i.val : V) value code) j = regValue code j := write_other code value i j h
example (out opcode index code : V) : effectDef.val.Evalb ![out,opcode,index,code] ↔
    out=effectValue opcode index code := by simp
example (i : Control) : registerKeyValue (V := V) (number i : V) =
    (ArithmeticControlData254.sourceRegister i : V) := registerKey_at i
example (i : Control) (branch : V) : nextValue (number i : V) branch =
    if branch=0 then (ArithmeticControlData254.successorNumber i false : V)
      else (ArithmeticControlData254.successorNumber i true : V) := next_at i branch
example (out q file : V) : liveDef.val.Evalb ![out,q,file] ↔ out=liveValue q file := by simp
example (q file : V) : controlValue (liveValue q file) = q := control_live q file
example (q file : V) : fileCodeValue (liveValue q file) = file := fileCode_live q file
example (state : V) (h : state≠0) : liveValue (controlValue state) (fileCodeValue state) = state :=
  live_decode state h
example (out q file : V) : transitionDef.val.Evalb ![out,q,file] ↔
    out=transitionValue q file := by simp
example (out state : V) : stepDef.val.Evalb ![out,state] ↔ out=stepValue state := by simp
example (state : V) : ∃! out : V, stepDef.val.Evalb ![out,state] := step_total state
example : stepValue (0 : V) = 0 := step_zero
example (q file : V) : stepValue (liveValue q file) = transitionValue q file := step_live q file
example (q file : V) (h : ArithmeticControlData254.opcodeValue q=0) :
    transitionValue q file=0 := transition_invalid q file h
example (q file : V) (h : ArithmeticControlData254.opcodeValue q=4) :
    transitionValue q file=0 := transition_halt q file h
example (q file : V) (h : ArithmeticControlData254.opcodeValue q=1) :
    transitionValue q file = liveValue (nextValue q (selectedValue file (registerKeyValue q)))
      (writeValue (registerKeyValue q) (selectedValue file (registerKeyValue q)+1) file) :=
  transition_inc q file h
example (q file : V) (h : ArithmeticControlData254.opcodeValue q=2) :
    transitionValue q file = liveValue (nextValue q (selectedValue file (registerKeyValue q)))
      (writeValue (registerKeyValue q) (selectedValue file (registerKeyValue q)-1) file) :=
  transition_decnz q file h
example (q file : V) (h : ArithmeticControlData254.opcodeValue q=3) :
    transitionValue q file = liveValue (nextValue q (selectedValue file (registerKeyValue q))) file :=
  transition_noop q file h
/-- The actual absent key0 is covered, without assuming an opcode premise. -/
example (file : V) : stepValue (liveValue 0 file)=0 := by
  rw [step_live]
  apply transition_invalid
  by_contra h
  obtain ⟨i,hi⟩ := (ArithmeticControlData254.opcodeValue_nonzero_iff (0 : V)).mp h
  have hn : 0 < number i := by simp [number]
  have hp : (0 : V) < (number i : V) := (Nat.cast_pos (α := V)).mpr hn
  exact (ne_of_gt hp) hi.symm
