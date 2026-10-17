import BusyBeaver.ZFC.ArithmeticStackCertificate254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticHistory254 ArithmeticStackTail254 ArithmeticStackCertificate254
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.provB_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.stackB_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.prov_of_value
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.prov_weaken
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.prov_truth
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.old_le_extendBound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.witness_le_extendBound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.one_le_extendBound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.prov_extend
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.stack_weaken
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.stack_full
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.stack_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.stack_head
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.stack_cons
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.stack_tail
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.stack_pushList
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.workingB_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.certifiedWorking_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.working_fields
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.working_weaken
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.working_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.working_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.certified_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticStackCertificate254.accepted_falsity_of_cache
example (B p x : V) (hp : p ≤ B) (hv : value p = x+1) : ProvB B x := prov_of_value hp hv
example (B C x : V) (hBC : B ≤ C) (hx : ProvB B x) : ProvB C x := prov_weaken hBC hx
example (B : V) (hB : 1 ≤ B) : ProvB B 0 := prov_truth hB
example (B p x : V) (hv : value p = x+1) : ProvB (extendBound B p) x := prov_extend hv
example (B p : V) : B ≤ extendBound B p ∧ p ≤ extendBound B p ∧ 1 ≤ extendBound B p :=
  ⟨old_le_extendBound B p, witness_le_extendBound B p, one_le_extendBound B p⟩
example (B z k : V) (hs : StackB B z) : ProvB B (first (tailIter k z)) := stack_full hs k
example (B z : V) (hs : StackB B z) : ProvB B (first z) := stack_head hs
example (B x z : V) (hx : ProvB B x) (hs : StackB B z) : StackB B (cantor x z) := stack_cons hx hs
example (B z : V) (hs : StackB B z) : StackB B (second z) := stack_tail hs
example (B C z : V) (hBC : B ≤ C) (hs : StackB B z) : StackB C z := stack_weaken hBC hs
example (B : V) (hB : 1 ≤ B) : StackB B 0 := stack_zero hB
example (B top stack d cache : V) :
    WorkingB B (cantor top (cantor stack (cantor d cache))) ↔
      ProvB B top ∧ ProvB B cache ∧ StackB B stack := working_fields B top stack d cache
example (B C w : V) (hBC : B ≤ C) (hw : WorkingB B w) : WorkingB C w := working_weaken hBC hw
example (B : V) (hB : 1 ≤ B) : WorkingB B 0 := working_zero hB
example : CertifiedWorking (0 : V) := certified_zero
example (B w : V) (hw : WorkingB B w) (hh : second (second (second w)) = 1) :
    ∃ p ≤ B, value p = 2 := accepted_falsity_of_cache hw hh
example (B x y z : V) (hx : ProvB B x) (hy : ProvB B y) (hs : StackB B z) :
    StackB B (pushList [x,y] z) := by
  apply stack_pushList B z [x,y] _ hs
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact hx
  · exact hy
