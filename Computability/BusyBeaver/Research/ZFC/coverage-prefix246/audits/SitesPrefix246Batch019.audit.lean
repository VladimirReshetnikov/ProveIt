import BusyBeaver.ZFC.SitesPrefix246Batch019

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_55
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_56
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_57

example : allSites SitePrefix246.checkSite [false, false, false, true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true, false, false, false]) = true := block_55

example : allSites SitePrefix246.checkSite [true, false, false, true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true, false, false, true]) = true := block_56

example : allSites SitePrefix246.checkSite [true, false, true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true, false, true]) = true := block_57
