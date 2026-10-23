import DiophantineConsistency.AnnotatedSchemaMaps

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedSchemaMaps

example (f : Form) : chainForm separationSteps f=rename rsep f := separation_chain f
example (f : Form) : chainForm functionFirstSteps f=rename rf1 f := functionFirst_chain f
example (f : Form) : chainForm functionSecondSteps f=rename rf2 f := functionSecond_chain f
example (f : Form) : chainForm imageSteps f=rename ri f := image_chain f
example (f : Form) : ∃ evidence,(chainProgram imageSteps).val.eval
    (inputCode (formCode f) (formCode (rename ri f)) evidence)=1 :=
  (exists_image_iff f _).mpr rfl
example (s : Step) (steps : List Step) (i o e : Nat)
    (h : chainValue (s::steps) (inputCode i o e)=1) :
    ∃ f : Form,i=formCode f ∧ o=formCode (chainForm (s::steps) f) :=
  chainValue_sound s steps i o e h

#eval (List.range 6).map rsep==[0,3,4,5,6,7]
#eval (List.range 6).map rf1==[1,2,3,4,5,6]
#eval (List.range 6).map rf2==[0,2,3,4,5,6]
#eval (List.range 6).map ri==[1,0,4,5,6,7]
#eval formCode (chainForm imageSteps (fAll (fMem 0 2)))==
  formCode (rename ri (fAll (fMem 0 2)))
#eval formCode (chainForm separationSteps (fEx (fMem 1 3)))==
  formCode (rename rsep (fEx (fMem 1 3)))
#eval chainValue imageSteps (inputCode 0 0 0)==0
#eval (chainProgram imageSteps).val.eval 0==0

#print axioms Step
#print axioms chainForm
#print axioms chainValue
#print axioms chainProgram
#print axioms exists_step_iff
#print axioms exists_chain_iff
#print axioms chainValue_sound
#print axioms chainProgram_primrec
#print axioms rsep_eq
#print axioms rf1_eq
#print axioms rf2_eq
#print axioms ri_eq
#print axioms exists_separation_iff
#print axioms exists_functionFirst_iff
#print axioms exists_functionSecond_iff
#print axioms exists_image_iff

example : (chainProgram separationSteps).val.nodeCount=7409 := separation_nodeCount
example : (chainProgram functionFirstSteps).val.nodeCount=3739 := functionFirst_nodeCount
example : (chainProgram functionSecondSteps).val.nodeCount=3741 := functionSecond_nodeCount
example : (chainProgram imageSteps).val.nodeCount=14753 := image_nodeCount
#print axioms separation_nodeCount
#print axioms functionFirst_nodeCount
#print axioms functionSecond_nodeCount
#print axioms image_nodeCount
