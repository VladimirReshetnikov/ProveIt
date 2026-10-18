import BusyBeaver.ZFC.SitesRouting245Batch001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_5
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_6
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_7
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_8

example : allSites SiteRouting245.checkSite [false, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, false]) = true := block_5

example : allSites SiteRouting245.checkSite [false, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false]) = true := block_6

example : allSites SiteRouting245.checkSite [true, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true]) = true := block_7

example : allSites SiteRouting245.checkSite [true, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true]) = true := block_8
