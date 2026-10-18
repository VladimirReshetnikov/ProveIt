import BusyBeaver.ZFC.SitesPrefix246Batch064

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_175
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_176
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_177

example : allSites SitePrefix246.checkSite [true, false, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, false, true]) = true := block_175

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, false]) = true := block_176

example : allSites SitePrefix246.checkSite [false, false, true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, false, false]) = true := block_177
