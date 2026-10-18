import BusyBeaver.ZFC.SitesRouting245Batch000

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_1
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_2
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_3
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_4

example : allSites SiteRouting245.checkSite [false, true]
      (descend TreeRouting245.tree [true, false]) = true := block_1

example : allSites SiteRouting245.checkSite [false, true, true]
      (descend TreeRouting245.tree [true, true, false]) = true := block_2

example : allSites SiteRouting245.checkSite [false, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, false]) = true := block_3

example : allSites SiteRouting245.checkSite [false, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, false]) = true := block_4
