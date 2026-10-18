import BusyBeaver.ZFC.SitesPrefix246Batch049

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_140
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_141

example : allSites SitePrefix246.checkSite [false, true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true, false]) = true := block_140

example : allSites SitePrefix246.checkSite [false, true, true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true, true, false]) = true := block_141
