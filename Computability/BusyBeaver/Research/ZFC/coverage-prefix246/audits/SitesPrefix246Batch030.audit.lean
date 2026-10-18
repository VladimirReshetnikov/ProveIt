import BusyBeaver.ZFC.SitesPrefix246Batch030

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_89
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_90
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_91

example : allSites SitePrefix246.checkSite [true, false, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false, true]) = true := block_89

example : allSites SitePrefix246.checkSite [true, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, true]) = true := block_90

example : allSites SitePrefix246.checkSite [false, false, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, true, false, false]) = true := block_91
