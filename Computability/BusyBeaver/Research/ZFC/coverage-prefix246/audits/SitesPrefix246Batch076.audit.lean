import BusyBeaver.ZFC.SitesPrefix246Batch076

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_203
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_204
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_205

example : allSites SitePrefix246.checkSite [false, false, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, false, false]) = true := block_203

example : allSites SitePrefix246.checkSite [true, false, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, false, true]) = true := block_204

example : allSites SitePrefix246.checkSite [false, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, false, false]) = true := block_205
