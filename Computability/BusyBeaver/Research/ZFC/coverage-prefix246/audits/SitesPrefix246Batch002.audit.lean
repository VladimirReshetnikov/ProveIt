import BusyBeaver.ZFC.SitesPrefix246Batch002

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_5
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_6
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_7
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_8

example : allSites SitePrefix246.checkSite [false, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, false]) = true := block_5

example : allSites SitePrefix246.checkSite [false, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false]) = true := block_6

example : allSites SitePrefix246.checkSite [true, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true]) = true := block_7

example : allSites SitePrefix246.checkSite [true, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true]) = true := block_8
