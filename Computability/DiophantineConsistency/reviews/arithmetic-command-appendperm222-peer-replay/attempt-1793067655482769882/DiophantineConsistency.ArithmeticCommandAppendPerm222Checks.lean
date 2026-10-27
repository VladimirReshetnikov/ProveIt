import DiophantineConsistency.ArithmeticCommandAppendPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandAppendPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandWordPerm222 ArithmeticCommandReplacePerm222 ArithmeticCommandAppendPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (right : V) : appendValue 1 right=replaceValue 0 right+1 := by
  have hz : tailValue (0 : V)=0 := le_antisymm (tail_le 0) (Arithmetic.zero_le _)
  simpa only [zero_add,hz,appendValue_zero] using appendValue_succ (0 : V) right
example (left right i : V) (h : ¬i≤left) : znth (history left right) i=0 := by
  rw [history_lookup,if_neg h]
example (p q : List EnumPerm.Cmd) :
    appendValue (encodeList (.nip::p)) (encodeList q)=encodeList (.nip::(p++q)) :=
  append_encodeList (.nip::p) q
example (left middle right : V) :
    appendValue (appendValue left middle) right=appendValue left (appendValue middle right) :=
  append_assoc left middle right

#print axioms history_defined
#print axioms history_seq
#print axioms history_length
#print axioms append_defined
#print axioms append_defined_delta
#print axioms history_lookup_le
#print axioms appendValue_succ
#print axioms appendValue_eq_zero
#print axioms history_lookup
#print axioms append_right_zero
#print axioms append_assoc
#print axioms append_encodeList
#print axioms append_total
#print axioms totalitySentence_true
#print axioms isigma1_proves_totality
#print axioms peano_proves_totality
end DiophantineConsistency.ArithmeticCommandAppendPerm222Checks
