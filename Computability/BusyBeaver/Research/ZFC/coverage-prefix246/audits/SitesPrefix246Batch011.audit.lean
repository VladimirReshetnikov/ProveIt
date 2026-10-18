import BusyBeaver.ZFC.SitesPrefix246Batch011

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_36
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_37
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_38

example : allSites SitePrefix246.checkSite [true, false, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, true]) = true := block_36

example : allSites SitePrefix246.checkSite [false, false, true, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true, false, false]) = true := block_37

example : allSites SitePrefix246.checkSite [true, false, true, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true, false, true]) = true := block_38
