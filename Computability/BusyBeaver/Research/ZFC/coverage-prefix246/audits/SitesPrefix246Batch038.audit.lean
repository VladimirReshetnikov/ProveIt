import BusyBeaver.ZFC.SitesPrefix246Batch038

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_111
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_112
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_113

example : allSites SitePrefix246.checkSite [true, true, false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, true, true]) = true := block_111

example : allSites SitePrefix246.checkSite [false, false, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false, false]) = true := block_112

example : allSites SitePrefix246.checkSite [false, true, false, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false, true, false]) = true := block_113
