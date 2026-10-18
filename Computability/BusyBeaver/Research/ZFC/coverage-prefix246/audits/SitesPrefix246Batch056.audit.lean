import BusyBeaver.ZFC.SitesPrefix246Batch056

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_155
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_156
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_157

example : allSites SitePrefix246.checkSite [false, false, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, false, false]) = true := block_155

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, false, true, false, false]) = true := block_156

example : allSites SitePrefix246.checkSite [true, false, true, false, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, false, true, false, true]) = true := block_157
