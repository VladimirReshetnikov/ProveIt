import BusyBeaver.ZFC.SitesRouting245Cut115

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.refine_115_0
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_115

example : allSites SiteRouting245.checkSite [false, true, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false]) = true := refine_115_0

example : allSites SiteRouting245.checkSite [true, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true]) = true := block_115
