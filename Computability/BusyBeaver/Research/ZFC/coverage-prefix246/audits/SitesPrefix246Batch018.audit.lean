import BusyBeaver.ZFC.SitesPrefix246Batch018

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_52
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_53
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_54

example : allSites SitePrefix246.checkSite [false, false, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, false, false, false]) = true := block_52

example : allSites SitePrefix246.checkSite [true, false, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, false, false, true]) = true := block_53

example : allSites SitePrefix246.checkSite [true, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true]) = true := block_54
