import DiophantineConsistency.AnnotatedParents

open DiophantineConsistency AnnotatedCodeArithmetic AnnotatedParents

example (fuel : Nat) (history expected : List Nat) (parents : Nat)
    (hf : expected.length≤fuel) :
    check fuel (listCode history) (listCode expected) parents=1 ↔
      ∃ indices : List Nat,parents=listCode indices ∧
        indices.map (fun i => history[i]?)=expected.map some :=
  check_raw_iff fuel history expected parents hf
example (history expected : List AnnotatedProofChecker.Judgment) (parents : Nat)
    (hf : expected.length≤3) :
    check 3 (listCode (history.map judgmentCode))
      (listCode (expected.map judgmentCode)) parents=1 ↔
        ∃ indices : List Nat,parents=listCode indices ∧
          indices.map (fun i => history[i]?)=expected.map some :=
  check_judgments_raw 3 history expected parents hf

-- Ordered success, swapped parents, missing references, and complete spines.
#eval check 3 (listCode [7,0]) (listCode [7,0]) (listCode [0,1])==1
#eval check 3 (listCode [7,8]) (listCode [7,8]) (listCode [1,0])==0
#eval check 3 (listCode [7]) (listCode [0]) (listCode [8])==0
#eval check 3 0 (listCode [0]) (listCode [0])==0
#eval check 3 0 0 (listCode [0])==0
#eval check 3 0 (listCode [0]) 0==0
#eval check 2 (listCode [1]) (listCode [1,1,1]) (listCode [0,0,0])==0
#eval (P.program 3).val.eval 0==1
example : (P.program 3).val.nodeCount=1101 := by decide
example : (P.program 3).optimize.val.nodeCount=1053 := by decide

#print axioms check
#print axioms check_nil
#print axioms check_cons
#print axioms check_lists
#print axioms check_raw_iff
#print axioms lookup_code_maps_iff
#print axioms check_judgments
#print axioms check_judgments_raw
#print axioms P.program
#print axioms program_input
#print axioms program_primrec
