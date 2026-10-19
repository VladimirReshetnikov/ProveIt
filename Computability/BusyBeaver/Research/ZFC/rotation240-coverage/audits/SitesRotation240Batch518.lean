import BusyBeaver.ZFC.SitesRotation240Batch518

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.block_522

example : allSites SiteRotation240.checkSite [false, false, false, false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false, false, false, false]) = true := block_522
