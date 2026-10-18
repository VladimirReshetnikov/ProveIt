import BusyBeaver.ZFC.SitesPrefix246Batch001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_1
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_2
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_3
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_4

example : allSites SitePrefix246.checkSite [false, true]
      (descend ActualTree254.tree [true, false]) = true := block_1

example : allSites SitePrefix246.checkSite [false, true, true]
      (descend ActualTree254.tree [true, true, false]) = true := block_2

example : allSites SitePrefix246.checkSite [false, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, false]) = true := block_3

example : allSites SitePrefix246.checkSite [false, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, false]) = true := block_4
