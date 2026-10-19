import BusyBeaver.ZFC.SitesRotation240

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.all_sites
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.actual_walk_checked
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.actual_walk_exists

example : allSites SiteRotation240.checkSite [] TreeRotation240.tree = true := all_sites

example (P : List Bool) (e : Edge) (d : Nat)
    (hw : walk SourceRotation240.program (SourceRotation240.program.nnodes + 1) SourceRotation240.program.root P 0 = some (e,d)) :
    SiteRotation240.checkSite (consume P d) e = true := actual_walk_checked P e d hw

example (P : List Bool) :
    ∃ e d, walk SourceRotation240.program (SourceRotation240.program.nnodes + 1) SourceRotation240.program.root P 0 = some (e,d) :=
  actual_walk_exists P
