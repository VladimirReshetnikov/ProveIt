import BusyBeaver.ZFC.SitesPrefix246Batch079

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_211
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_212
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_213
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_214

example : allSites SitePrefix246.checkSite [true, false, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, false, true]) = true := block_211

example : allSites SitePrefix246.checkSite [true, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, true]) = true := block_212

example : allSites SitePrefix246.checkSite [true, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, true]) = true := block_213

example : allSites SitePrefix246.checkSite [false, false, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false, false]) = true := block_214
