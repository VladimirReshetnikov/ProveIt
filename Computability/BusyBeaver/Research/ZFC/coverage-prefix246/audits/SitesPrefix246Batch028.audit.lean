import BusyBeaver.ZFC.SitesPrefix246Batch028

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_83
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_84
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_85

example : allSites SitePrefix246.checkSite [false, false, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false, false]) = true := block_83

example : allSites SitePrefix246.checkSite [true, false, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false, true]) = true := block_84

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, true, false, false]) = true := block_85
