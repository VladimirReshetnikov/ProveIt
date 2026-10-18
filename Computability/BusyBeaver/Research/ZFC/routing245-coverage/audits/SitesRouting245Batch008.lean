import BusyBeaver.ZFC.SitesRouting245Batch008

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_26
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_27
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_28
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_29

example : allSites SiteRouting245.checkSite [false, false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false]) = true := block_26

example : allSites SiteRouting245.checkSite [true, false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, true]) = true := block_27

example : allSites SiteRouting245.checkSite [true, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, true]) = true := block_28

example : allSites SiteRouting245.checkSite [false, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, false]) = true := block_29
