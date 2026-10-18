import BusyBeaver.ZFC.SitesPrefix246Batch063

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_172
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_173
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_174

example : allSites SitePrefix246.checkSite [false, true, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, true, false]) = true := block_172

example : allSites SitePrefix246.checkSite [true, true, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, true, true]) = true := block_173

example : allSites SitePrefix246.checkSite [false, false, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, false, false]) = true := block_174
