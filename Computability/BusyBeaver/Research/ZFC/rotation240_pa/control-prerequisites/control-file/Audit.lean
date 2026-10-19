import BusyBeaver.ZFC.ArithmeticControlFile

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC.ArithmeticControlFile

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFile.reg_file
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFile.file_reg
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFile.selected_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFile.write_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFile.write_other
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFile.live_ne_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFile.control_live
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFile.fileCode_live
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlFile.live_decode

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (values : Fin 9 → V) (i : Fin 9) : regValue (fileValue values) i = values i :=
  reg_file values i
example (x : V) : fileValue (regValue x) = x := file_reg x
example (x : V) (i : Fin 9) : selectedValue x (i.val : V) = regValue x i :=
  selected_at x i
example (x v : V) (i : Fin 9) : regValue (writeValue (i.val : V) v x) i = v :=
  write_at x v i
example (x v : V) (i j : Fin 9) (h : i ≠ j) :
    regValue (writeValue (i.val : V) v x) j = regValue x j := write_other x v i j h
example (q x : V) : liveValue q x ≠ 0 := live_ne_zero q x
example (q x : V) : controlValue (liveValue q x) = q := control_live q x
example (q x : V) : fileCodeValue (liveValue q x) = x := fileCode_live q x
example (x : V) (h : x ≠ 0) : liveValue (controlValue x) (fileCodeValue x) = x :=
  live_decode x h
example (i : Fin 9) : 𝚺₁-Function₁[V] (fun x => tupleProjection 8 x i) via projectionDef 8 i :=
  projection_defined 8 i
example : 𝚺₁-Function₂[V] liveValue via liveDef := live_defined
