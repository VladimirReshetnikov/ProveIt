import BusyBeaver.ZFC.RMDagContextSubstitution
open SetTheory.BusyBeaver.ZFC.RMDag
open SetTheory.BusyBeaver.ZFC.RMDagContextSubstitution

#print axioms SetTheory.BusyBeaver.ZFC.RMDagContextSubstitution.Replacement.symm
#print axioms SetTheory.BusyBeaver.ZFC.RMDagContextSubstitution.forward
#print axioms SetTheory.BusyBeaver.ZFC.RMDagContextSubstitution.run_iff
#print axioms SetTheory.BusyBeaver.ZFC.RMDagContextSubstitution.iter_forward
#print axioms SetTheory.BusyBeaver.ZFC.RMDagContextSubstitution.iterHalts_iff

example {p q : Prog} {safe : Edge → Prop} {entry : Nat}
    (rep : Replacement p q safe entry) : Replacement q p safe entry := rep.symm
example {p q : Prog} {safe : Edge → Prop} {entry : Nat}
    (rep : Replacement p q safe entry) {e : Edge} {R R' : Regs} {x : Exit}
    (h : Run p e R x R') (hs : safe e) : Run q e R x R' := forward rep h hs
example {p q : Prog} {safe : Edge → Prop} {entry : Nat}
    (rep : Replacement p q safe entry) {e : Edge} (hs : safe e)
    (R R' : Regs) (x : Exit) : Run p e R x R' ↔ Run q e R x R' := run_iff rep hs R R' x
example {p q : Prog} {safe : Edge → Prop} {entry : Nat}
    (rep : Replacement p q safe entry) (hroot : p.root = q.root)
    (hs : safe (.node p.root)) {R : Regs} (h : IterHalts p R) : IterHalts q R :=
  iter_forward rep hroot hs h
example {p q : Prog} {safe : Edge → Prop} {entry : Nat}
    (rep : Replacement p q safe entry) (hroot : p.root = q.root)
    (hs : safe (.node p.root)) (R : Regs) : IterHalts p R ↔ IterHalts q R :=
  iterHalts_iff rep hroot hs R
example {p q : Prog} {safe : Edge → Prop}
    (rep : Replacement p q safe 6) (hroot : p.root = q.root)
    (hs : safe (.node p.root)) (R : Regs) : IterHalts q R ↔ IterHalts p R :=
  (iterHalts_iff rep hroot hs R).symm
