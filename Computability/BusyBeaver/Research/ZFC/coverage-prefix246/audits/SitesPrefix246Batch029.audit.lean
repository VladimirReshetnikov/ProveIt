import BusyBeaver.ZFC.SitesPrefix246Batch029

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_86
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_87
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_88

example : allSites SitePrefix246.checkSite [true, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, true, false, true]) = true := block_86

example : allSites SitePrefix246.checkSite [true, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, true, true]) = true := block_87

example : allSites SitePrefix246.checkSite [false, false, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, false]) = true := block_88
