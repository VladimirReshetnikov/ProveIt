import BusyBeaver.ZFC.SitesPrefix246Batch025

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_74
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_75
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_76

example : allSites SitePrefix246.checkSite [true, true, false, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false, true, true]) = true := block_74

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, true, false, false]) = true := block_75

example : allSites SitePrefix246.checkSite [true, false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, true, false, true]) = true := block_76
