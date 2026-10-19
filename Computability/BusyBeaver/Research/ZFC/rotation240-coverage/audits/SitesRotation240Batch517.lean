import BusyBeaver.ZFC.SitesRotation240Batch517

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.block_521

example : allSites SiteRotation240.checkSite [true, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, true]) = true := block_521
