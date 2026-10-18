import BusyBeaver.ZFC.SitesPrefix246Batch032

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_95
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_96
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_97

example : allSites SitePrefix246.checkSite [true, false, false, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, false, true]) = true := block_95

example : allSites SitePrefix246.checkSite [true, false, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true]) = true := block_96

example : allSites SitePrefix246.checkSite [true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true]) = true := block_97
