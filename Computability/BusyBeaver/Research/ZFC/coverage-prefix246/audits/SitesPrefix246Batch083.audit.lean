import BusyBeaver.ZFC.SitesPrefix246Batch083

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_221
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_222
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_223
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_224

example : allSites SitePrefix246.checkSite [true, true, false, false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false, true, true]) = true := block_221

example : allSites SitePrefix246.checkSite [true, false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, true]) = true := block_222

example : allSites SitePrefix246.checkSite [true, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, true]) = true := block_223

example : allSites SitePrefix246.checkSite [true, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, true]) = true := block_224
