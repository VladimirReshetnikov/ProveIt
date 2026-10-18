import BusyBeaver.ZFC.SitesPrefix246Batch070

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_189
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_190

example : allSites SitePrefix246.checkSite [true, true, true, false, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, true, true, true]) = true := block_189

example : allSites SitePrefix246.checkSite [false, true, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, true, false]) = true := block_190
