import BusyBeaver.ZFC.SitesPrefix246Batch065

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_178
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_179
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_180

example : allSites SitePrefix246.checkSite [true, false, true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, false, true]) = true := block_178

example : allSites SitePrefix246.checkSite [true, true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, true]) = true := block_179

example : allSites SitePrefix246.checkSite [false, false, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, false, false]) = true := block_180
