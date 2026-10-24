import DiophantineConsistency.AnnotatedLine

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofChecker AnnotatedProofCode AnnotatedCodeArithmetic AnnotatedLine

example (history : List Judgment) (line : Nat)
    (h : check (listCode (history.map judgmentCode)) line=1) :
    ∃ original : Line,(AnnotatedRename.decodeRow line).output=judgmentCode original.rule.output ∧
      (AnnotatedRename.decodeRow line).input=listCode original.parents ∧ original.valid history=true :=
  check_sound history line h
example (history : List Judgment) (line : Line) (h : line.valid history=true) :
    ∃ code : Nat,(AnnotatedRename.decodeRow code).output=judgmentCode line.rule.output ∧
      (AnnotatedRename.decodeRow code).input=listCode line.parents ∧
      check (listCode (history.map judgmentCode)) code=1 := check_complete history line h

-- Positive certificates exist for both a premise-free rule and a binder rule.
example : ∃ code : Nat,check 0 code=1 := by
  obtain ⟨code,_,_,hc⟩ := check_complete [] ⟨.eqRefl [] 0,[]⟩ (by decide)
  exact ⟨code,hc⟩
example (G : List Form) (a : Form) :
    ∃ code : Nat,check (listCode [judgmentCode ⟨G.map (rename Nat.succ),a⟩]) code=1 := by
  obtain ⟨code,_,_,hc⟩ := check_complete [⟨G.map (rename Nat.succ),a⟩]
    ⟨.allI G a,[0]⟩ (by simp [Line.valid,Rule.side,Rule.premises])
  exact ⟨code,hc⟩

#eval check 0 0==0
#eval rowCheck 0 ⟨17,0,0,0,0,0⟩==0
#eval P.program.val.eval 0==0
#eval optimizedProgram.val.eval 0==0
example : P.program.val.nodeCount=24589 := by decide
example : optimizedProgram.val.nodeCount=22715 := by decide

#print axioms equal
#print axioms rowCheck
#print axioms AnnotatedLine.check
#print axioms premises_length
#print axioms rowCheck_sound
#print axioms AnnotatedLine.check_sound
#print axioms rowCheck_complete
#print axioms check_complete
#print axioms P.program
#print axioms program_input
#print axioms program_primrec
