import BusyBeaver.ZFC.SitesPrefix246Batch015

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_43
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_44
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.block_45

example : allSites SitePrefix246.checkSite [true, true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, true]) = true := block_43

example : allSites SitePrefix246.checkSite [false, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, false]) = true := block_44

example : allSites SitePrefix246.checkSite [false, false, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, false, false]) = true := block_45
