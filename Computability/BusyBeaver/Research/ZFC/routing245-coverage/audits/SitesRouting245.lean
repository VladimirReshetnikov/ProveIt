import BusyBeaver.ZFC.SitesRouting245

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.all_sites
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.actual_walk_checked
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.actual_walk_exists

example : allSites SiteRouting245.checkSite [] TreeRouting245.tree = true := all_sites

example (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d)) :
    SiteRouting245.checkSite (consume P d) e = true := actual_walk_checked P e d hw

example (P : List Bool) :
    ∃ e d, walk ProgramRouting245.program (ProgramRouting245.program.nnodes + 1) ProgramRouting245.program.root P 0 = some (e,d) :=
  actual_walk_exists P
