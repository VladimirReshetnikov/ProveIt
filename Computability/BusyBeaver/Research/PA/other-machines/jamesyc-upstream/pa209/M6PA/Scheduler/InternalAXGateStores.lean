module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.InternalAXMacro
public import M6PA.Scheduler.InternalAXGateCompare
@[expose] public section
open M6.Arithmetic.PA
namespace M6.Arithmetic.PA.InternalTrace.ModelAX
open M6 M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
noncomputable def workCode (s : Store V) (bottom n x y : V) : V :=
  ?[n,s.t,stackCode s.stack bottom,s.a,s.d,s.h,x,y,s.l]
lemma work_valid (s : Store V) (bottom n x y : V) : CodedSource.ValidStore (workCode s bottom n x y) := by
  simp [workCode,CodedSource.ValidStore]
  norm_num
lemma work_registers (s : Store V) (bottom n x y : V) :
    CodedSource.registers (workCode s bottom n x y)=![n,s.t,stackCode s.stack bottom,s.a,s.d,s.h,x,y,s.l] := by
  simp [funext_iff,Fin.forall_fin_succ,CodedSource.registers,workCode]
lemma work_zero (s : Store V) (bottom n : V) : workCode s bottom n 0 0=storeCode s bottom n := rfl
lemma copy_a_store (s : Store V) (bottom n : V) :
    CodedSource.drainTwoEnd 3 7 6 s.a (workCode s bottom n 0 0)=
      workCode {s with a:=0} bottom n s.a s.a := by
  apply CodedSource.registers_ext (CodedSource.drainTwoEnd_valid _ _ _ _ _ (work_valid s bottom n 0 0)) (work_valid _ _ _ _ _)
  rw [CodedSource.drainTwoEnd_registers _ _ _ _ _ (work_valid s bottom n 0 0),work_registers,work_registers]
  simp [funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write]
lemma y_to_x_store (s : Store V) (bottom n y : V) :
    CodedSource.drainEnd 7 6 y (workCode s bottom n 0 y)=workCode s bottom n y 0 := by
  apply CodedSource.registers_ext (CodedSource.drainEnd_valid _ _ _ _ (work_valid s bottom n 0 y)) (work_valid _ _ _ _ _)
  rw [CodedSource.drainEnd_registers _ _ _ _ (work_valid s bottom n 0 y),work_registers,work_registers]
  simp [funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write]
lemma d_to_h_store (s : Store V) (bottom n x : V) (hh : s.h=0) :
    CodedSource.drainEnd 4 5 s.d (workCode s bottom n x 0)=workCode {s with d:=0,h:=s.d} bottom n x 0 := by
  apply CodedSource.registers_ext (CodedSource.drainEnd_valid _ _ _ _ (work_valid s bottom n x 0)) (work_valid _ _ _ _ _)
  rw [CodedSource.drainEnd_registers _ _ _ _ (work_valid s bottom n x 0),work_registers,work_registers]
  simp [funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write,hh]
lemma compare_store (s : Store V) (bottom n x y : V) :
    AXGateModel.compareEnd (workCode s bottom n x y)=
      workCode {s with t:=if s.h=x then 0 else s.t,h:=0} bottom n 0 y := by
  have hv := work_valid s bottom n x y
  have hguard : CodedSource.registers (CodedSource.guardStore (workCode s bottom n x y) 0 0)=
      PhysicalRegisters.write (PhysicalRegisters.write
        (CodedSource.registers (workCode s bottom n x y)) 5 0) 6 0 := by
    have h5 : CodedSource.registers (CodedSource.replace 5 (workCode s bottom n x y) 0)=
        PhysicalRegisters.write (CodedSource.registers (workCode s bottom n x y)) 5 0 :=
      CodedSource.registers_replace _ _ hv 5
    have h6 : CodedSource.registers (CodedSource.guardStore (workCode s bottom n x y) 0 0)=
        PhysicalRegisters.write (CodedSource.registers (CodedSource.replace 5 (workCode s bottom n x y) 0)) 6 0 :=
      CodedSource.registers_replace _ _ (CodedSource.replace_valid _ _ hv 5) 6
    rw [h6,h5]
  have hr : CodedSource.registers (CodedSource.replace 1 (CodedSource.guardStore (workCode s bottom n x y) 0 0) 0)=
      PhysicalRegisters.write (CodedSource.registers (CodedSource.guardStore (workCode s bottom n x y) 0 0)) 1 0 :=
    CodedSource.registers_replace _ _ (CodedSource.guardStore_valid _ 0 0 hv) 1
  apply CodedSource.registers_ext (AXGateModel.compareEnd_valid _ hv) (work_valid _ _ _ _ _)
  have hh : CodedSource.registers (workCode s bottom n x y) 5=s.h := by rw [work_registers];rfl
  have hx : CodedSource.registers (workCode s bottom n x y) 6=x := by rw [work_registers];rfl
  unfold AXGateModel.compareEnd
  rw [hh,hx]
  by_cases he : s.h=x
  · simp only [he,ite_true]
    rw [hr,hguard,work_registers,work_registers]
    simp [funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write,he]
  · simp only [he,ite_false]
    rw [hguard,work_registers,work_registers]
    simp [funext_iff,Fin.forall_fin_succ,PhysicalRegisters.write,he]
#print axioms compare_store
end M6.Arithmetic.PA.InternalTrace.ModelAX

