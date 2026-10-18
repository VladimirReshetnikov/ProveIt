import BusyBeaver.ZFC.SitesRouting245Batch003

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_11
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_12
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_13

example : allSites SiteRouting245.checkSite [true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true]) = true := block_11

example : allSites SiteRouting245.checkSite [false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false]) = true := block_12

example : allSites SiteRouting245.checkSite [true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true]) = true := block_13
