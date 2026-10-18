import BusyBeaver.ZFC.SitesPrefix246Batch048

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_137
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_138
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_139

example : allSites SitePrefix246.checkSite [true, true, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true]) = true := block_137

example : allSites SitePrefix246.checkSite [false, false, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false, false]) = true := block_138

example : allSites SitePrefix246.checkSite [true, false, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false, true]) = true := block_139
