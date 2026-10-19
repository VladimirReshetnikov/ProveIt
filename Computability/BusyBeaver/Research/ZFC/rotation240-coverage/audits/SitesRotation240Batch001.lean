import BusyBeaver.ZFC.SitesRotation240Batch001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.block_1

example : allSites SiteRotation240.checkSite [false, true]
      (descend TreeRotation240.tree [true, false]) = true := block_1
