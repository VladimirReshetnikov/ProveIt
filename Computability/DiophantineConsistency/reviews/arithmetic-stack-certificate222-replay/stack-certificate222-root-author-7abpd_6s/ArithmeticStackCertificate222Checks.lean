import DiophantineConsistency.ArithmeticStackCertificate222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticStackCertificate222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor ArithmeticStackTail254
open ArithmeticStackCertificate222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- Every internal offset, including beyond the stream's numeric code, is covered.
example {B z : V} (hs : StackB B z) (k : V) :
    ∃ p≤B, ArithmeticHistory222.value p=first (tailIter k z)+1 := stack_full hs k

-- Repeated proof-bearing entries and empty suffixes are allowed.
example {B x : V} (hB : 1≤B) (hx : ProvB B x) :
    StackB B (cantor x (cantor x 0)) := stack_cons hx (stack_cons hx (stack_zero hB))

example : CertifiedWorking (0 : V) := certified_zero

-- The extracted witness is accepted by the actual C222 checker, not the old one.
example {B w : V} (hw : WorkingB B w) (hc : second (second (second w))=1) :
    ∃ p≤B, ArithmeticHistory222.checkDef.val.Evalb ![p,1] := by
  obtain ⟨p,hp,hv⟩ := accepted_falsity_of_cache hw hc
  refine ⟨p,hp,?_⟩
  simpa [one_add_one_eq_two] using hv

#print axioms provB_definable
#print axioms stackB_definable
#print axioms certifiedWorking_definable
#print axioms stack_full
#print axioms stack_cons
#print axioms stack_tail
#print axioms stack_weaken
#print axioms working_fields
#print axioms certified_zero
#print axioms accepted_falsity_of_cache
end DiophantineConsistency.ArithmeticStackCertificate222Checks
