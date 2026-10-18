import BusyBeaver.ZFC.SitesPrefix246Batch020

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_58
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_59
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_60

example : allSites SitePrefix246.checkSite [false, true, true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true, true, false]) = true := block_58

example : allSites SitePrefix246.checkSite [true, true, true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true, true, true]) = true := block_59

example : allSites SitePrefix246.checkSite [false, false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false]) = true := block_60
