import BusyBeaver.ZFC.SitesPrefix246Batch042

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_122
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_123
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_124

example : allSites SitePrefix246.checkSite [false, false, false, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false, false, false]) = true := block_122

example : allSites SitePrefix246.checkSite [true, false, false, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false, false, true]) = true := block_123

example : allSites SitePrefix246.checkSite [true, false, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false, true]) = true := block_124
