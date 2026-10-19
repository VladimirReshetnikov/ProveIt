import BusyBeaver.ZFC.SitesRotation240Batch520

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.block_524

example : allSites SiteRotation240.checkSite [false, true, false, false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false, false, true, false]) = true := block_524
