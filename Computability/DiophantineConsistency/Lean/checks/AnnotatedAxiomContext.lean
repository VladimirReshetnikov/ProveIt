import DiophantineConsistency.AnnotatedAxiomContext

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedContext (contextCode)
open AnnotatedAxiomContext

example (expected fuel certificate : Nat) (h : checkNat expected fuel certificate=1) :
    ∃ G : List Form,expected=contextCode G ∧ AllAxioms G := checkNat_sound expected fuel certificate h
example (G : List Form) :
    (∃ fuel certificate,P.program.val.eval (inputCode (contextCode G) fuel certificate)=1) ↔
      AllAxioms G := exists_program_iff G
example (tag : AnnotatedProofChecker.AxiomTag) :
    ∃ fuel certificate,checkNat (contextCode [tag.form]) fuel certificate=1 := by
  apply checkNat_complete
  intro f hf
  simp only [List.mem_singleton] at hf
  exact hf ▸ tag.sound

#eval checkNat 1 0 0==1
#eval checkNat 0 0 0==0
#eval checkNat 1 0 1==0
#eval checkNat 1 1 (AnnotatedCodeArithmetic.listCode [AnnotatedAxiomDispatch.inputCode 9 0 0])==0
#eval P.program.val.eval (inputCode 1 0 0)==1
#eval P.program.val.eval (inputCode 0 0 0)==0
example : P.program.val.nodeCount=58281 := by decide
example : optimizedProgram.val.nodeCount=53187 := by decide

#print axioms AllAxioms
#print axioms contextCode_ne_zero
#print axioms step
#print axioms scan
#print axioms scan_sound
#print axioms finish_context
#print axioms checkNat
#print axioms checkNat_sound
#print axioms AnnotatedAxiomContext.run
#print axioms run_complete
#print axioms checkNat_complete
#print axioms exists_checkNat_iff
#print axioms P.stepProgram
#print axioms P.program
#print axioms program_input
#print axioms program_sound
#print axioms exists_program_iff
#print axioms program_primrec
