import BusyBeaver.ZFC.SitesRotation240Batch524

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.block_528

example : allSites SiteRotation240.checkSite [false, true, true, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, true, true, false]) = true := block_528
