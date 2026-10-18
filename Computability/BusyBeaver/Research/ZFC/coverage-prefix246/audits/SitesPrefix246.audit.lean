import BusyBeaver.ZFC.SitesPrefix246

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.all_sites
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.actual_walk_checked
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.actual_walk_exists

example : allSites SitePrefix246.checkSite [] ActualTree254.tree = true := all_sites

example (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 = some (e,d)) :
    SitePrefix246.checkSite (consume P d) e = true := actual_walk_checked P e d hw

example (P : List Bool) :
    ∃ e d, walk Prog254.program (Prog254.program.nnodes + 1) Prog254.program.root P 0 = some (e,d) :=
  actual_walk_exists P
