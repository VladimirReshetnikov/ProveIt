import BusyBeaver.ZFC.SitesPrefix246Batch040

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_117
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_118
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_119

example : allSites SitePrefix246.checkSite [false, false, true, true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true, true, false, false]) = true := block_117

example : allSites SitePrefix246.checkSite [true, false, true, true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true, true, false, true]) = true := block_118

example : allSites SitePrefix246.checkSite [true, true, true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true, true, true]) = true := block_119
