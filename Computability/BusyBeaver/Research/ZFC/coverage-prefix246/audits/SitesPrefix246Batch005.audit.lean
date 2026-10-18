import BusyBeaver.ZFC.SitesPrefix246Batch005

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_14
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_15
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_16
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_17

example : allSites SitePrefix246.checkSite [false, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false]) = true := block_14

example : allSites SitePrefix246.checkSite [true, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true]) = true := block_15

example : allSites SitePrefix246.checkSite [true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true]) = true := block_16

example : allSites SitePrefix246.checkSite [false, false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false]) = true := block_17
