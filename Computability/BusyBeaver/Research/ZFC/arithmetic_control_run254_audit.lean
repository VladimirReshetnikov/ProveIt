import BusyBeaver.ZFC.ArithmeticControlRun254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlRun254 ArithmeticControlStep254 ArithmeticControlFrame254
open ArithmeticCantor ArithmeticMachineRunFromPerm252 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.controlRun_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.controlRun_defined_delta
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.controlRun_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.controlRun_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.controlRun_succ
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.controlRun_add
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.controlRun_halted
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.controlRun_total
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.halts_iff_entry
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.projection_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.physicalValues_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.entry_empty
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.initialControl_number
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.initialValue_live_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.entry_boot
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlRun254.halts_iff_blank

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (out time initial : V) : controlRunDef.val.Evalb ![out,time,initial] ↔
    out=controlRun time initial := by simp
example : 𝚫₁-Function₂[V] controlRun via controlRunDeltaDef := inferInstance
example : 𝚺₁-Function₂[V] controlRun := inferInstance
example (initial : V) : controlRun 0 initial=initial := controlRun_zero initial
example (time initial : V) : controlRun (time+1) initial=
    ArithmeticControlStep254.stepValue (controlRun time initial) := controlRun_succ time initial
example (t u initial : V) : controlRun (t+u) initial=controlRun u (controlRun t initial) :=
  controlRun_add t u initial
example (time : V) : controlRun time 0=0 := controlRun_halted time
example (time initial : V) : ∃! out : V, controlRunDef.val.Evalb ![out,time,initial] :=
  controlRun_total time initial
example (i : Control) (file count gap : V) :
    (∃ time : V, controlRun time (liveValue (number i : V) file)=0) ↔
      (∃ time : V, first (runFrom time (entryValue (number i : V) file count gap))=0) :=
  halts_iff_entry i file count gap
example (n : Nat) (i : Fin (n+1)) : tupleProjection n (0 : V) i=0 := projection_zero n i
example : physicalValues (0 : V)=List.replicate 9 0 := physicalValues_zero
example (file count gap : V) : entryValue (number (resolveControl []) : V) file count gap=
    ArithmeticSitePerm252.startValue (physicalValues file) count gap [] := entry_empty file count gap
example : number initialControl=1 := initialControl_number
example : initialValue (V := V)=liveValue 1 0 := initialValue_live_one
example : entryValue (number initialControl : V) 0 56 0=
    (ArithmeticBootstrapPerm252.bootCode : V) := entry_boot
example : (∃ time : V, controlRun time initialValue=0) ↔
    (∃ time : V, first (ArithmeticMachineRunPerm252.run time)=0) := halts_iff_blank
example : initialValue (V := V)≠0 := by rw [initialValue_live_one]; exact live_ne_zero _ _
example (time : V) (h : controlRun time initialValue=0) :
    ∃ clock : V, first (ArithmeticMachineRunPerm252.run clock)=0 :=
  halts_iff_blank.mp ⟨time,h⟩
