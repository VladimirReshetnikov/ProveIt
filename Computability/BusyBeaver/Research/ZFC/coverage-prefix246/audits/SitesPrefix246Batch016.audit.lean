import BusyBeaver.ZFC.SitesPrefix246Batch016

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_46
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_47
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_48

example : allSites SitePrefix246.checkSite [false, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, false]) = true := block_46

example : allSites SitePrefix246.checkSite [true, true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true, true]) = true := block_47

example : allSites SitePrefix246.checkSite [false, true, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, true, false]) = true := block_48
