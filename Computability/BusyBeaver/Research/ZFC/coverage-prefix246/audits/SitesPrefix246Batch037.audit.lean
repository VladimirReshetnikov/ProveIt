import BusyBeaver.ZFC.SitesPrefix246Batch037

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_108
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_109
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_110

example : allSites SitePrefix246.checkSite [true, true, false, false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, true, true]) = true := block_108

example : allSites SitePrefix246.checkSite [false, false, true, false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, true, false, false]) = true := block_109

example : allSites SitePrefix246.checkSite [true, false, true, false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, true, false, true]) = true := block_110
