import BusyBeaver.ZFC.SitesRouting245Batch004

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_14
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_15
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_16

example : allSites SiteRouting245.checkSite [false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false]) = true := block_14

example : allSites SiteRouting245.checkSite [true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true]) = true := block_15

example : allSites SiteRouting245.checkSite [true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true]) = true := block_16
