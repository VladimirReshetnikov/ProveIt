import BusyBeaver.ZFC.SitesPrefix246Batch044

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_127
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_128

example : allSites SitePrefix246.checkSite [true, true, false, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true]) = true := block_127

example : allSites SitePrefix246.checkSite [false, true, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false]) = true := block_128
