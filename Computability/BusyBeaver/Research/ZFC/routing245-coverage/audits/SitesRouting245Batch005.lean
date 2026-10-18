import BusyBeaver.ZFC.SitesRouting245Batch005

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_17
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_18
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_19

example : allSites SiteRouting245.checkSite [false, false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false]) = true := block_17

example : allSites SiteRouting245.checkSite [true, false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true]) = true := block_18

example : allSites SiteRouting245.checkSite [false, false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false]) = true := block_19
