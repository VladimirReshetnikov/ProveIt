import BusyBeaver.ZFC.SitesRotation240Batch519

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.block_523

example : allSites SiteRotation240.checkSite [true, false, false, false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false, false, false, true]) = true := block_523
