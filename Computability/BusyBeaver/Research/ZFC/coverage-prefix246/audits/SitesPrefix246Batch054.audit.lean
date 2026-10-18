import BusyBeaver.ZFC.SitesPrefix246Batch054

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_151
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_152

example : allSites SitePrefix246.checkSite [false, true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, false]) = true := block_151

example : allSites SitePrefix246.checkSite [false, true, true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, true, false]) = true := block_152
