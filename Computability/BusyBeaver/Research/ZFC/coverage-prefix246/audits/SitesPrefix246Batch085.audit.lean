import BusyBeaver.ZFC.SitesPrefix246Batch085

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_229
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_230
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_231
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_232

example : allSites SitePrefix246.checkSite [false, false, false, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, false, false, false]) = true := block_229

example : allSites SitePrefix246.checkSite [true, false, false, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, false, false, true]) = true := block_230

example : allSites SitePrefix246.checkSite [true, false, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, false, true]) = true := block_231

example : allSites SitePrefix246.checkSite [true, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, true]) = true := block_232
