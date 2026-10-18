import BusyBeaver.ZFC.SitesPrefix246Batch017

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_49
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_50
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_51

example : allSites SitePrefix246.checkSite [false, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, true, true, false, false]) = true := block_49

example : allSites SitePrefix246.checkSite [true, false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, true, true, false, true]) = true := block_50

example : allSites SitePrefix246.checkSite [true, true, true, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, true, true, true]) = true := block_51
