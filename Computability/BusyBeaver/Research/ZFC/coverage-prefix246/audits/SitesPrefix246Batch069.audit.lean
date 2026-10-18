import BusyBeaver.ZFC.SitesPrefix246Batch069

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_187
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_188

example : allSites SitePrefix246.checkSite [false, true, false, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, true, false]) = true := block_187

example : allSites SitePrefix246.checkSite [false, true, true, false, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, true, true, false]) = true := block_188
