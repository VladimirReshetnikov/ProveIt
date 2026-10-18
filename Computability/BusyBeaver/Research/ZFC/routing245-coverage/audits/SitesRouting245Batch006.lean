import BusyBeaver.ZFC.SitesRouting245Batch006

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_20
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_21
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_22

example : allSites SiteRouting245.checkSite [true, false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true]) = true := block_20

example : allSites SiteRouting245.checkSite [false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false]) = true := block_21

example : allSites SiteRouting245.checkSite [false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false]) = true := block_22
