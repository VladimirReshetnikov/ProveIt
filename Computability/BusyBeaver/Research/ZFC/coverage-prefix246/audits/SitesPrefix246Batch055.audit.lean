import BusyBeaver.ZFC.SitesPrefix246Batch055

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_153
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_154

example : allSites SitePrefix246.checkSite [true, true, true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, true, true]) = true := block_153

example : allSites SitePrefix246.checkSite [true, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, true]) = true := block_154
