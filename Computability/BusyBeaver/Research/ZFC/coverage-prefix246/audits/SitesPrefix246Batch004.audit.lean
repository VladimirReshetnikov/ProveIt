import BusyBeaver.ZFC.SitesPrefix246Batch004

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_11
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_12
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_13

example : allSites SitePrefix246.checkSite [true, false, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, false, true]) = true := block_11

example : allSites SitePrefix246.checkSite [false, true, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, true, false]) = true := block_12

example : allSites SitePrefix246.checkSite [true, true, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, true, true]) = true := block_13
