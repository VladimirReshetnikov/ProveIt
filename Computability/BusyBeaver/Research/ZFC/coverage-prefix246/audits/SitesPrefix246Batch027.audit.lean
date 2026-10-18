import BusyBeaver.ZFC.SitesPrefix246Batch027

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_80
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_81
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_82

example : allSites SitePrefix246.checkSite [true, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true]) = true := block_80

example : allSites SitePrefix246.checkSite [false, true, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, true, false]) = true := block_81

example : allSites SitePrefix246.checkSite [true, true, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, true, true]) = true := block_82
