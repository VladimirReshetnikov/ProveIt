import BusyBeaver.ZFC.SitesPrefix246Batch082

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_219
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_220

example : allSites SitePrefix246.checkSite [false, false, false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false, false]) = true := block_219

example : allSites SitePrefix246.checkSite [false, true, false, false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false, true, false]) = true := block_220
