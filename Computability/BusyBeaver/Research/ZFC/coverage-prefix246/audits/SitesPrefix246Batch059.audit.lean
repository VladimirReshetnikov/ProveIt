import BusyBeaver.ZFC.SitesPrefix246Batch059

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_164
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_165

example : allSites SitePrefix246.checkSite [true, false, true, true, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, true, true, false, true]) = true := block_164

example : allSites SitePrefix246.checkSite [true, true, true, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, true, true, true]) = true := block_165
