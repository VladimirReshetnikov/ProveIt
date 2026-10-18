import BusyBeaver.ZFC.SitesPrefix246Batch008

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_24
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_25
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_26
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_27

example : allSites SitePrefix246.checkSite [true, true, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true, true]) = true := block_24

example : allSites SitePrefix246.checkSite [false, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, false]) = true := block_25

example : allSites SitePrefix246.checkSite [false, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false, false]) = true := block_26

example : allSites SitePrefix246.checkSite [true, false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false, true]) = true := block_27
