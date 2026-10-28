import DiophantineConsistency.ArithmeticCommandPreservationPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandPreservationPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticCode254
open ArithmeticStackCertificate222 ArithmeticCommandStepPerm222
open ArithmeticCommandPreservationPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- Every internal raw selector and working code; no source/runtime invariant supplied.
example {raw w : V} (hw : CertifiedWorking w) (hs : stepValue raw w≠0) :
    CertifiedWorking (stepValue raw w-1) := certified_step hw hs

-- Cached false1 is only useful here when an actual certificate exists.
example {raw w : V} (hw : CertifiedWorking w) (hs : stepValue raw w=0) :
    ∃ proof, ArithmeticHistory222.checkDef.val.Evalb ![proof,1] := by
  obtain ⟨proof,hp⟩ := certified_halt hw hs
  exact ⟨proof,by simpa [one_add_one_eq_two] using hp⟩

-- Successful MP uses the old top as minor and old cache as major.
example {B t s h : V} (b : V) (ht : ProvB B t) (hh : ProvB B h)
    (hs : StackB B s) (hm : wim t b=h) :
    CertifiedWorking (stateValue b (cantor 0 s) b 0) :=
  certified_mp_success b ht hh hs hm

-- AX keeps old d as GEN label and rho8 fourth input; physical fields are y=p,x=q.
example {B t s h : V} (d p q c : V) (ht : ProvB B t) (hh : ProvB B h)
    (hs : StackB B s) :
    CertifiedWorking (stateValue (gateValue (d+q) (h+p) c)
      (axStackValue (d+q) h (h+p) c d t s) 0 0) :=
  certified_ax (d+q) (h+p) c d ht hh hs

-- Label collisions give a checked truth gate, never a false1 axiom.
example (a b : V) : ∃ proof, ArithmeticHistory222.value proof=gateValue a b a+1 :=
  gate_witness a b a

#print axioms old_le_witnessBound
#print axioms mem_le_witnessBound
#print axioms gate_witness
#print axioms certified_mp_success
#print axioms certified_ax
#print axioms effect_preserves
#print axioms certified_step
#print axioms certified_halt
end DiophantineConsistency.ArithmeticCommandPreservationPerm222Checks
