import BusyBeaver.ZFC.SitesPrefix246Batch003

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_9
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_10

example : allSites SitePrefix246.checkSite [false, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, false]) = true := block_9

example : allSites SitePrefix246.checkSite [false, false, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, false, false]) = true := block_10
