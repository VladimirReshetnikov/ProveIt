import BusyBeaver.ZFC.SitesRouting245Cut084

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_84

example : allSites SiteRouting245.checkSite [false, true, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, true, false]) = true := block_84
