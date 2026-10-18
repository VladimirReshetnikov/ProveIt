import BusyBeaver.ZFC.SitesRouting245Batch011

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_37
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_38
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_39

example : allSites SiteRouting245.checkSite [false, false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, false]) = true := block_37

example : allSites SiteRouting245.checkSite [true, false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, true]) = true := block_38

example : allSites SiteRouting245.checkSite [true, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true]) = true := block_39
