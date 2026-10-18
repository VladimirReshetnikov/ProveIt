import BusyBeaver.ZFC.SitesPrefix246Batch067

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_183
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_184

example : allSites SitePrefix246.checkSite [false, true, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, true, false]) = true := block_183

example : allSites SitePrefix246.checkSite [true, true, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, true, true]) = true := block_184
