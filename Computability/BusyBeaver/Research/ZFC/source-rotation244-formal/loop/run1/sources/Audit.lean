import BusyBeaver.ZFC.RMDagLoopRotation

open SetTheory.BusyBeaver.ZFC.RMDag
open SetTheory.BusyBeaver.ZFC.RMDagLoopRotation

#print axioms SetTheory.BusyBeaver.ZFC.RMDagLoopRotation.normalFile_src
#print axioms SetTheory.BusyBeaver.ZFC.RMDagLoopRotation.normalFile_dst
#print axioms SetTheory.BusyBeaver.ZFC.RMDagLoopRotation.normalFile_other
#print axioms SetTheory.BusyBeaver.ZFC.RMDagLoopRotation.old_normal
#print axioms SetTheory.BusyBeaver.ZFC.RMDagLoopRotation.new_normal
#print axioms SetTheory.BusyBeaver.ZFC.RMDagLoopRotation.run_iff

example (R : Regs) (src dst : Nat) : normalFile R src dst src = 0 :=
  normalFile_src R src dst
example (R : Regs) {src dst : Nat} (h : src ≠ dst) :
    normalFile R src dst dst = R dst + R src + 1 := normalFile_dst R h
example (R : Regs) {src dst i : Nat} (hs : i ≠ src) (hd : i ≠ dst) :
    normalFile R src dst i = R i := normalFile_other R hs hd
example {p : Prog} {n l b src dst : Nat}
    (hn : p.nodes n = (.node l, .inc dst))
    (hl : p.nodes l = (.decnz src, .node b))
    (hb : p.nodes b = (.inc dst, .cont 2)) (h : src ≠ dst) (R : Regs) :
    Run p (.node n) R .normal (normalFile R src dst) := old_normal hn hl hb h R
example {p : Prog} {n l src dst : Nat}
    (hn : p.nodes n = (.inc dst, .node l))
    (hl : p.nodes l = (.decnz src, .cont 2)) (h : src ≠ dst) (R : Regs) :
    Run p (.node n) R .normal (normalFile R src dst) := new_normal hn hl h R
example {p q : Prog} {n l b n' l' src dst : Nat}
    (hn : p.nodes n = (.node l, .inc dst))
    (hl : p.nodes l = (.decnz src, .node b))
    (hb : p.nodes b = (.inc dst, .cont 2))
    (hn' : q.nodes n' = (.inc dst, .node l'))
    (hl' : q.nodes l' = (.decnz src, .cont 2)) (h : src ≠ dst)
    (R R' : Regs) (x : Exit) :
    Run p (.node n) R x R' ↔ Run q (.node n') R x R' := run_iff hn hl hb hn' hl' h R R' x
example {p : Prog}
    (hn : p.nodes 6 = (.node 5, .inc 0))
    (hl : p.nodes 5 = (.decnz 6, .node 4))
    (hb : p.nodes 4 = (.inc 0, .cont 2)) (R : Regs) :
    Run p (.node 6) R .normal (upd (upd R 0 (R 0 + R 6 + 1)) 6 0) :=
  old_normal hn hl hb (by decide) R
example {p : Prog}
    (hn : p.nodes 6 = (.inc 0, .node 5))
    (hl : p.nodes 5 = (.decnz 6, .cont 2)) (R : Regs) :
    Run p (.node 6) R .normal (upd (upd R 0 (R 0 + R 6 + 1)) 6 0) :=
  new_normal hn hl (by decide) R
