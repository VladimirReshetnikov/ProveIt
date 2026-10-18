import BusyBeaver.ZFC.SitesPrefix246Batch036

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_105
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_106
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_107

example : allSites SitePrefix246.checkSite [true, true, false, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false, true, true]) = true := block_105

example : allSites SitePrefix246.checkSite [false, false, false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, false]) = true := block_106

example : allSites SitePrefix246.checkSite [false, true, false, false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, true, false]) = true := block_107
