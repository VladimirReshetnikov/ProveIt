import BusyBeaver.ZFC.SitesPrefix246Batch043

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_125
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_126

example : allSites SitePrefix246.checkSite [false, false, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, false]) = true := block_125

example : allSites SitePrefix246.checkSite [false, true, false, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, true, false]) = true := block_126
