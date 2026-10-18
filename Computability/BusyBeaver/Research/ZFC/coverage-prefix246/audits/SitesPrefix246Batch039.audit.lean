import BusyBeaver.ZFC.SitesPrefix246Batch039

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_114
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_115
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_116

example : allSites SitePrefix246.checkSite [true, true, false, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false, true, true]) = true := block_114

example : allSites SitePrefix246.checkSite [false, false, true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true, false, false]) = true := block_115

example : allSites SitePrefix246.checkSite [true, false, true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true, false, true]) = true := block_116
