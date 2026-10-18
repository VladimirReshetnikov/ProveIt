import BusyBeaver.ZFC.SitesRouting245Pilot1609

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SitesRouting245Pilot1609

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245Pilot1609.actual_leaf
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245Pilot1609.site_checked

example : twalk TreeRouting245.tree path 0 = some (instruction, 42) := actual_leaf

example : walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1)
    ProgramRouting245.program.root path 0 = some (instruction, 42) := by
  calc
    _ = twalk TreeRouting245.tree path 0 := by
      simpa only [List.drop_zero] using TreeRouting245.walk_eq_tree path 0
    _ = some (instruction, 42) := actual_leaf

example : SiteRouting245.checkSite path instruction = true := site_checked

example : SiteRouting245.runTo (some (SiteRouting245.physical 2 (by decide), true)) path
    (SiteRouting245.target (breakPath 1 path) (SiteRouting245.allOnes (stripPath false 1 path))
      0 (.plain .unchanged)) = true :=
  (SiteRouting245.check_decnz path 2 (by decide) site_checked).1

example : SiteRouting245.runTo (some (SiteRouting245.physical 2 (by decide), false)) path
    (SiteRouting245.target (incPath path) (SiteRouting245.allOnes path)
      1 (.plain (.decrement (SiteRouting245.physical 2 (by decide))))) = true :=
  (SiteRouting245.check_decnz path 2 (by decide) site_checked).2
