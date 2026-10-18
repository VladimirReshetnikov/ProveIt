import BusyBeaver.ZFC.SitesRouting245Cut051

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.refine_51_0
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_51

example : allSites SiteRouting245.checkSite [false, true, true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true, true, false]) = true := refine_51_0

example : allSites SiteRouting245.checkSite [true, true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true, true]) = true := block_51
