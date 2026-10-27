import DiophantineConsistency.ArithmeticCommandFetchPerm222
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandFetchPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandWordPerm222 ArithmeticCommandFetchPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

example (np : V) : tailValue (first (fetchValue (1 : V) np))=0 := by
  have h : (1 : V)=(0 : V)+1 := by simp
  rw [h, raw_continuation]
  have hz : cantor (0 : V) 0=0 := by simp [cantor, triangle]
  simpa only [hz] using tail_nip (0 : V)

example (np : V) : second (fetchValue (1 : V) np)=np := by
  simpa using next_continuation (0 : V) np
example (pl np : V) (hp : pl≠0) : tailValue (first (fetchValue pl np))+1≤pl :=
  continuation_progress pl np hp
example (s : EnumPerm.St) : first (fetchValue s.pl s.np)=(EnumPerm.fetch s).1 := raw_nat s

#print axioms fetch_defined
#print axioms fetch_total
#print axioms fetch_continuation
#print axioms continuation_progress
#print axioms new_candidate_bound
#print axioms fetch_nat
#print axioms raw_nat
#print axioms next_nat
end DiophantineConsistency.ArithmeticCommandFetchPerm222Checks
