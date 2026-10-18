import BusyBeaver.ZFC.SitesPrefix246Batch010

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_32
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_33
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_34
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_35

example : allSites SitePrefix246.checkSite [true, false, true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false, true]) = true := block_32

example : allSites SitePrefix246.checkSite [true, true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, true]) = true := block_33

example : allSites SitePrefix246.checkSite [false, false, false, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, false, false]) = true := block_34

example : allSites SitePrefix246.checkSite [true, false, false, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, false, true]) = true := block_35
