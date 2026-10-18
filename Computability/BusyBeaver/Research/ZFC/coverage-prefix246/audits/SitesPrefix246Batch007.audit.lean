import BusyBeaver.ZFC.SitesPrefix246Batch007

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_21
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_22
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_23

example : allSites SitePrefix246.checkSite [false, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false]) = true := block_21

example : allSites SitePrefix246.checkSite [false, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, false]) = true := block_22

example : allSites SitePrefix246.checkSite [false, true, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, false]) = true := block_23
