import BusyBeaver.ZFC.SitesPrefix246Batch023

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_67
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_68
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_69

example : allSites SitePrefix246.checkSite [true, false, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, false, true]) = true := block_67

example : allSites SitePrefix246.checkSite [false, false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, false]) = true := block_68

example : allSites SitePrefix246.checkSite [true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true]) = true := block_69
