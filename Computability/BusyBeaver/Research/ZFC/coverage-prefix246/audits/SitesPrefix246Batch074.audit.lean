import BusyBeaver.ZFC.SitesPrefix246Batch074

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_197
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_198
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_199

example : allSites SitePrefix246.checkSite [true, false, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, true, true, false, true]) = true := block_197

example : allSites SitePrefix246.checkSite [true, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, true, true, true]) = true := block_198

example : allSites SitePrefix246.checkSite [false, false, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, false, false]) = true := block_199
