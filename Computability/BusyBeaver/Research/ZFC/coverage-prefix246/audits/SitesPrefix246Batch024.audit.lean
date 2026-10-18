import BusyBeaver.ZFC.SitesPrefix246Batch024

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_70
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_71
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_72
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_73

example : allSites SitePrefix246.checkSite [true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true]) = true := block_70

example : allSites SitePrefix246.checkSite [true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true]) = true := block_71

example : allSites SitePrefix246.checkSite [false, false, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false, false]) = true := block_72

example : allSites SitePrefix246.checkSite [false, true, false, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false, true, false]) = true := block_73
