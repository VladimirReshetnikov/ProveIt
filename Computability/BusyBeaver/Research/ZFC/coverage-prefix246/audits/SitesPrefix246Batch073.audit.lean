import BusyBeaver.ZFC.SitesPrefix246Batch073

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_195
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_196

example : allSites SitePrefix246.checkSite [true, true, false, true, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, true, false, true, true]) = true := block_195

example : allSites SitePrefix246.checkSite [false, false, true, true, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, true, true, false, false]) = true := block_196
