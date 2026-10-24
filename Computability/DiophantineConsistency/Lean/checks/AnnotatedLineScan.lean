import DiophantineConsistency.AnnotatedLineScan

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofChecker AnnotatedCodeArithmetic AnnotatedLineScan

example (goal fuel proofCode : Nat) (h : checkNat goal fuel proofCode=1) :
    ∃ j : Judgment,goal=judgmentCode j ∧ j.Provable := checkNat_sound goal fuel proofCode h
example (j : Judgment) :
    (∃ fuel proofCode,P.program.val.eval (inputCode (judgmentCode j) fuel proofCode)=1) ↔
      j.Provable := exists_program_iff j
example (G : List Form) (a : Form) :
    (∃ fuel proofCode,P.program.val.eval (inputCode (judgmentCode ⟨G,a⟩) fuel proofCode)=1) ↔
      Prov G a := exists_program_iff ⟨G,a⟩
example : ∃ fuel proofCode,checkNat (judgmentCode ⟨[],fEq 0 0⟩) fuel proofCode=1 :=
  checkNat_complete ⟨[],fEq 0 0⟩ (.P_eqRefl [] 0)

-- No completed history, unconsumed input, and malformed raw first line.
#eval checkNat 0 0 0==0
#eval checkNat 0 0 1==0
#eval checkNat 0 1 1==0
#eval P.program.val.eval (inputCode 0 0 0)==0
#eval P.program.val.eval (inputCode 0 0 1)==0
#eval optimizedProgram.val.eval (inputCode 0 0 0)==0
example : P.program.val.nodeCount=24891 := by decide
example : optimizedProgram.val.nodeCount=23017 := by decide

#print axioms step
#print axioms scan
#print axioms scan_sound
#print axioms finish
#print axioms finish_history
#print axioms checkNat
#print axioms checkNat_sound
#print axioms AnnotatedLineScan.run
#print axioms scan_list
#print axioms run_complete
#print axioms checkNat_complete
#print axioms exists_checkNat_iff
#print axioms P.stepProgram
#print axioms P.program
#print axioms program_input
#print axioms program_sound
#print axioms exists_program_iff
#print axioms program_primrec
