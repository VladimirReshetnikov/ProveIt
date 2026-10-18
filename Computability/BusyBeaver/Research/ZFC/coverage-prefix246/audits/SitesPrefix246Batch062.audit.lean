import BusyBeaver.ZFC.SitesPrefix246Batch062

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_170
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_171

example : allSites SitePrefix246.checkSite [false, true, true, false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, true, true, false]) = true := block_170

example : allSites SitePrefix246.checkSite [true, true, true, false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, true, true, true]) = true := block_171
