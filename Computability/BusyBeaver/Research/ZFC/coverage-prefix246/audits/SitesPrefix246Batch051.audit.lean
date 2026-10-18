import BusyBeaver.ZFC.SitesPrefix246Batch051

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_144
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_145
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_146

example : allSites SitePrefix246.checkSite [true, false, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, false, true]) = true := block_144

example : allSites SitePrefix246.checkSite [false, false, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, false, false]) = true := block_145

example : allSites SitePrefix246.checkSite [true, false, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, false, true]) = true := block_146
