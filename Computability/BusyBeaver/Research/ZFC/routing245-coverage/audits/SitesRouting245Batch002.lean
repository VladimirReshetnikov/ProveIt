import BusyBeaver.ZFC.SitesRouting245Batch002

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_9
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_10

example : allSites SiteRouting245.checkSite [false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false]) = true := block_9

example : allSites SiteRouting245.checkSite [false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false]) = true := block_10
