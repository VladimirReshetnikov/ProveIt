import BusyBeaver.ZFC.SitesRouting245Cut124

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.refine_124_0
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_124

example : allSites SiteRouting245.checkSite [false, false, false, true, false, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false, true, false, false, false]) = true := refine_124_0

example : allSites SiteRouting245.checkSite [false, false, true, false, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false, true, false, false]) = true := block_124
