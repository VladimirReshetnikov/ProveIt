import BusyBeaver.ZFC.SitesPrefix246Batch035

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_102
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_103
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_104

example : allSites SitePrefix246.checkSite [false, false, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false, false]) = true := block_102

example : allSites SitePrefix246.checkSite [false, false, true, false, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false, true, false, false]) = true := block_103

example : allSites SitePrefix246.checkSite [true, false, true, false, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false, true, false, true]) = true := block_104
