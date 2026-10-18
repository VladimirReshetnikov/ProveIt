import BusyBeaver.ZFC.SitesRouting245Pilot6324

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SitesRouting245Pilot6324

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245Pilot6324.actual_leaf
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245Pilot6324.site_checked

example : twalk TreeRouting245.tree path 0 = some (instruction, 13) := actual_leaf

example : walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1)
    ProgramRouting245.program.root path 0 = some (instruction, 13) := by
  calc
    _ = twalk TreeRouting245.tree path 0 := by
      simpa only [List.drop_zero] using TreeRouting245.walk_eq_tree path 0
    _ = some (instruction, 13) := actual_leaf

example : SiteRouting245.checkSite path instruction = true := site_checked
