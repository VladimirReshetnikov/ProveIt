import BusyBeaver.ZFC.SitesPrefix246Batch060

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_166
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_167

example : allSites SitePrefix246.checkSite [false, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, false, false]) = true := block_166

example : allSites SitePrefix246.checkSite [false, true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, false, true, false]) = true := block_167
