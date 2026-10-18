import BusyBeaver.ZFC.SitesPrefix246Batch075

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_200
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_201
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_202

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, false, true, false, false]) = true := block_200

example : allSites SitePrefix246.checkSite [true, false, true, false, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, false, true, false, true]) = true := block_201

example : allSites SitePrefix246.checkSite [true, true, false, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, false, true, true]) = true := block_202
