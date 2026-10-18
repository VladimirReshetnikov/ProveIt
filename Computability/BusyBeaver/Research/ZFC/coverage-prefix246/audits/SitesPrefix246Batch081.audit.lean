import BusyBeaver.ZFC.SitesPrefix246Batch081

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_217
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_218

example : allSites SitePrefix246.checkSite [false, true, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true, false]) = true := block_217

example : allSites SitePrefix246.checkSite [true, true, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true, true]) = true := block_218
