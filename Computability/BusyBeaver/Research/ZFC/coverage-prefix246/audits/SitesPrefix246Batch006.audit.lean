import BusyBeaver.ZFC.SitesPrefix246Batch006

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_18
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_19
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_20

example : allSites SitePrefix246.checkSite [true, false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true]) = true := block_18

example : allSites SitePrefix246.checkSite [false, true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false]) = true := block_19

example : allSites SitePrefix246.checkSite [true, true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true]) = true := block_20
