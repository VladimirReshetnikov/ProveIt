import BusyBeaver.ZFC.SitesRotation240Batch525

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.block_529

example : allSites SiteRotation240.checkSite [true, true, true, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, true, true, true]) = true := block_529
