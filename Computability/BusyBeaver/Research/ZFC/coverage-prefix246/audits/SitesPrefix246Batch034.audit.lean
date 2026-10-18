import BusyBeaver.ZFC.SitesPrefix246Batch034

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_100
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_101

example : allSites SitePrefix246.checkSite [true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true]) = true := block_100

example : allSites SitePrefix246.checkSite [true, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, true]) = true := block_101
