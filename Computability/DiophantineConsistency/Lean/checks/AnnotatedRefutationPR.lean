import DiophantineConsistency.AnnotatedRefutationPR

open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency DiophantineConsistency
open AnnotatedProofCode AnnotatedRefutationPR

example (raw : Nat) (h : P.program.val.eval raw=1) :
    ∃ f : Form,raw.unpair.1=formCode f ∧ BProv ZFCax_s [] f := program_raw_sound raw h
example (f : Form) :
    (∃ certificate,P.program.val.eval (Nat.pair (formCode f) certificate)=1) ↔ BProv ZFCax_s [] f :=
  exists_program_iff f
example :
    (∃ certificate,refutationProgram.val.eval certificate=1) ↔ BProv ZFCax_s [] fBot :=
  exists_refutation_iff
example :
    (¬∃ certificate,refutationProgram.val.eval certificate=1) ↔ ¬BProv ZFCax_s [] fBot :=
  no_refutation_iff
example : ∃ certificate,value (formCode (fEq 0 0)) certificate=1 := by
  apply complete
  exact ⟨[],by simp,by simpa only [List.append_nil] using Prov.P_eqRefl [] 0⟩

#eval value (formCode fBot) 0==0
#eval refutationProgram.val.eval 0==0
#eval optimizedProgram.val.eval 0==0
example : refutationProgram.val.nodeCount=83281 := by decide
example : optimizedProgram.val.nodeCount=76313 := by decide

#print axioms value
#print axioms forkCode_eq_iff
#print axioms raw_sound
#print axioms sound
#print axioms complete
#print axioms exists_value_iff
#print axioms P.program
#print axioms program_input
#print axioms program_raw_sound
#print axioms exists_program_iff
#print axioms program_primrec
#print axioms refutationProgram
#print axioms refutationProgram_input
#print axioms exists_refutation_iff
#print axioms no_refutation_iff
#print axioms refutationProgram_primrec
