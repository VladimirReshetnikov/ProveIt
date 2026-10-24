import DiophantineConsistency.AnnotatedContext

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedContext

example (i o e : Nat) (h : checkNat i o e=1) :
    ∃ G : List Form,i=contextCode G ∧ o=contextCode (G.map (rename Nat.succ)) :=
  checkNat_sound i o e h
example (G : List Form) (o : Nat) :
    (∃ e,checkNat (contextCode G) o e=1) ↔ o=contextCode (G.map (rename Nat.succ)) :=
  exists_check_iff G o
example (f : Form) : ∃ e,checkNat (contextCode [fAll f])
    (contextCode [rename Nat.succ (fAll f)]) e=1 :=
  (exists_check_iff [fAll f] _).mpr rfl
example (G : List Form) : G.length≤contextCode G := length_le_contextCode G

#eval checkNat 1 1 0==1
#eval checkNat 1 0 0==0
#eval checkNat 0 0 0==0
#eval checkNat (AnnotatedRename.atomCode 2) 1 0==0
#eval checkNat (contextCode [fBot]) (contextCode [fBot]) 0==0
#eval localCheck (contextCode [fBot]) (contextCode [fBot]) 0==0

#print axioms contextCode
#print axioms contextCode_injective
#print axioms localCheck
#print axioms localCheck_sound
#print axioms scan_sound
#print axioms checkNat_sound
#print axioms step_cons
#print axioms scan_complete
#print axioms length_le_contextCode
#print axioms exists_check_iff
