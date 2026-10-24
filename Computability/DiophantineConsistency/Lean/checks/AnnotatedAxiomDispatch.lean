import DiophantineConsistency.AnnotatedAxiomDispatch

open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency DiophantineConsistency
open AnnotatedProofCode AnnotatedAxiomDispatch

example (raw : Nat) (h : P.program.val.eval raw=1) :
    ∃ f : Form,ZFCax_s f ∧ raw.unpair.2.unpair.1=formCode f := program_sound raw h
example (f : Form) :
    (∃ tag evidence,P.program.val.eval (inputCode tag (formCode f) evidence)=1) ↔ ZFCax_s f :=
  exists_program_iff f
example (tag : AnnotatedProofChecker.AxiomTag) :
    ∃ evidence,value (tagNumber tag) (formCode tag.form) evidence=1 := complete tag
example (tag goal evidence : Nat) (h : 9≤tag) : value tag goal evidence=0 := by
  simp only [value,if_neg (by omega : ¬tag<9)]
example (f : Form) : ∃ evidence,
    P.program.val.eval (inputCode 6 (formCode (sealF (Sep_form f))) evidence)=1 := by
  obtain ⟨e,he⟩ := complete (.separation f)
  exact ⟨e,by simpa only [program_input,tagNumber,AnnotatedProofChecker.AxiomTag.form] using he⟩
example (f : Form) : ∃ evidence,
    P.program.val.eval (inputCode 7 (formCode (sealF (Repl_form f))) evidence)=1 := by
  obtain ⟨e,he⟩ := complete (.replacement f)
  exact ⟨e,by simpa only [program_input,tagNumber,AnnotatedProofChecker.AxiomTag.form] using he⟩

-- Executing supplied branch programs eagerly would evaluate enormous fixed
-- formula codes. These source controls exercise the guarded invalid-tag path.
#eval value 9 0 0==0
#eval value 99 0 0==0
example : P.program.val.nodeCount=58007 := by decide
example : optimizedProgram.val.nodeCount=52913 := by decide

#print axioms fixedValue
#print axioms separationValue
#print axioms replacementValue
#print axioms body
#print axioms value
#print axioms sound
#print axioms complete
#print axioms exists_value_iff
#print axioms P.bodyProgram
#print axioms P.program
#print axioms program_input
#print axioms program_sound
#print axioms exists_program_iff
#print axioms program_primrec
