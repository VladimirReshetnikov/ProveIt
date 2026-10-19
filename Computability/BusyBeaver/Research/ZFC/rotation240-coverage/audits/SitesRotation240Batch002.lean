import BusyBeaver.ZFC.SitesRotation240Batch002

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.block_2

example : allSites SiteRotation240.checkSite [false, true, true]
      (descend TreeRotation240.tree [true, true, false]) = true := block_2
