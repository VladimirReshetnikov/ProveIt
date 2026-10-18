import BusyBeaver.ZFC.SitesPrefix246Batch047

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_134
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_135
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_136

example : allSites SitePrefix246.checkSite [true, true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, true]) = true := block_134

example : allSites SitePrefix246.checkSite [false, false, true, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false, false]) = true := block_135

example : allSites SitePrefix246.checkSite [true, false, true, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false, true]) = true := block_136
