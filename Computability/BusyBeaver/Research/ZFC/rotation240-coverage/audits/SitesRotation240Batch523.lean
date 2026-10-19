import BusyBeaver.ZFC.SitesRotation240Batch523

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.block_527

example : allSites SiteRotation240.checkSite [false, true, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, true, false]) = true := block_527
