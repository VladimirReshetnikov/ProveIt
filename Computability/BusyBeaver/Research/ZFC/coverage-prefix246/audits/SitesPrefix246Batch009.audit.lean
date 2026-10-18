import BusyBeaver.ZFC.SitesPrefix246Batch009

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_28
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_29
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_30
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_31

example : allSites SitePrefix246.checkSite [true, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, true]) = true := block_28

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, false]) = true := block_29

example : allSites SitePrefix246.checkSite [false, false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false, false, false]) = true := block_30

example : allSites SitePrefix246.checkSite [true, false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false, false, true]) = true := block_31
