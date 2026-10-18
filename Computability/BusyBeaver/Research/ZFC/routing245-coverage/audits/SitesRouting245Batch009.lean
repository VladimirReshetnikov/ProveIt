import BusyBeaver.ZFC.SitesRouting245Batch009

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_30
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_31
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_32
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_33

example : allSites SiteRouting245.checkSite [false, false, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, false]) = true := block_30

example : allSites SiteRouting245.checkSite [true, false, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true]) = true := block_31

example : allSites SiteRouting245.checkSite [true, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, true]) = true := block_32

example : allSites SiteRouting245.checkSite [true, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, true]) = true := block_33
