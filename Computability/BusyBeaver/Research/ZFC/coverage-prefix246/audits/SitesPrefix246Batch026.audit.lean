import BusyBeaver.ZFC.SitesPrefix246Batch026

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_77
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_78
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_79

example : allSites SitePrefix246.checkSite [true, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, true, true]) = true := block_77

example : allSites SitePrefix246.checkSite [false, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, false]) = true := block_78

example : allSites SitePrefix246.checkSite [true, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true]) = true := block_79
