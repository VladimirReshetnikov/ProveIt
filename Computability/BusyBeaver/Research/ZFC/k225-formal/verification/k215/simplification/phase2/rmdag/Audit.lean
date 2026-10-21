import BusyBeaver.ZFC.RMDag
namespace RMDagDetAudit
open SetTheory.BusyBeaver.ZFC.RMDag

theorem deterministic {p : Prog} {e : Edge} {R : Regs} {x y : Exit} {R' R'' : Regs}
    (h : Run p e R x R') (h' : Run p e R y R'') : x = y ∧ R' = R'' := run_det h h'

#print axioms deterministic
end RMDagDetAudit
