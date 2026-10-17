import BusyBeaver.ZFC.ArithmeticCommandPreservation254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254
open ArithmeticHistory254 (value)
open ArithmeticStackCertificate254 ArithmeticCommandStep254 ArithmeticCommandPreservation254
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.working_state
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.certified_state
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.someState_sub_one
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.old_le_witnessBound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.mem_le_witnessBound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.prov_at_witnessBound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.gate_witness
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.certified_mp_success
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.certified_ax
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.effect_preserves
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.certified_step
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticCommandPreservation254.certified_halt
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example {raw w : V} (hw : CertifiedWorking w) (hz : stepValue raw w ≠ 0) :
    CertifiedWorking (stepValue raw w - 1) := certified_step hw hz
example {raw w : V} (hw : CertifiedWorking w) (hz : stepValue raw w = 0) :
    ∃ p : V, value p = 2 := certified_halt hw hz
example (k x y u t s d h : V) (hw : CertifiedWorking (stateValue t s d h))
    (hz : effectValue k x y u t s d h ≠ 0) :
    CertifiedWorking (effectValue k x y u t s d h - 1) := effect_preserves k x y u t s d h hw hz
example (B t s d h : V) : WorkingB B (stateValue t s d h) ↔
    ProvB B t ∧ ProvB B h ∧ StackB B s := working_state B t s d h
example {B t s d h : V} (ht : ProvB B t) (hh : ProvB B h) (hs : StackB B s) :
    CertifiedWorking (stateValue t s d h) := certified_state ht hh hs
example (t s d h : V) : someState t s d h - 1 = stateValue t s d h := someState_sub_one t s d h
example (B : V) (ps : List V) : B ≤ witnessBound B ps := old_le_witnessBound B ps
example (B : V) (ps : List V) (p : V) (hp : p ∈ ps) : p ≤ witnessBound B ps :=
  mem_le_witnessBound B ps hp
example (a b c : V) : ∃ p, value p = gateValue a b c + 1 := gate_witness a b c
example {B t s h : V} (b : V) (ht : ProvB B t) (hh : ProvB B h) (hs : StackB B s)
    (hm : wim t b = h) : CertifiedWorking (stateValue b (cantor 0 s) b 0) :=
  certified_mp_success b ht hh hs hm
example {B t s h : V} (a b c u : V) (ht : ProvB B t) (hh : ProvB B h) (hs : StackB B s) :
    CertifiedWorking (stateValue (gateValue a b c) (axStackValue a h b c u t s) 0 0) :=
  certified_ax a b c u ht hh hs
example {B t s h : V} (a u : V) (ht : ProvB B t) (hh : ProvB B h) (hs : StackB B s) :
    CertifiedWorking (stateValue 0 (axStackValue a h a a u t s) 0 0) := by
  simpa [gateValue] using certified_ax a a a u ht hh hs
example {B s d : V} (hs : StackB B s) : CertifiedWorking (stateValue 0 s d 0) :=
  certified_state (prov_truth hs.1) (prov_truth hs.1) hs
example {B t s d h : V} (ht : ProvB B t) (hh : ProvB B h) (hs : StackB B s) :
    CertifiedWorking (stateValue h (cantor t s) d h) := certified_state hh hh (stack_cons ht hs)
example {B t s d : V} (ht : ProvB B t) (hs : StackB B s) :
    CertifiedWorking (stateValue t (second s) d (first s)) :=
  certified_state ht (stack_head hs) (stack_tail hs)
