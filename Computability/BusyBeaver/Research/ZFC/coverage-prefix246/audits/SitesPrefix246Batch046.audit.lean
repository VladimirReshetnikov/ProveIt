import BusyBeaver.ZFC.SitesPrefix246Batch046

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_131
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_132
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_133

example : allSites SitePrefix246.checkSite [true, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, true]) = true := block_131

example : allSites SitePrefix246.checkSite [false, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, false]) = true := block_132

example : allSites SitePrefix246.checkSite [false, true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, false]) = true := block_133
