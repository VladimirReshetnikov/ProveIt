import BusyBeaver.ZFC.SitesPrefix246Batch077

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_206
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_207
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_208
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_209

example : allSites SitePrefix246.checkSite [true, false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, false, true]) = true := block_206

example : allSites SitePrefix246.checkSite [true, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, true]) = true := block_207

example : allSites SitePrefix246.checkSite [true, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, true]) = true := block_208

example : allSites SitePrefix246.checkSite [false, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, false]) = true := block_209
