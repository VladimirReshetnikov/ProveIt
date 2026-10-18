import BusyBeaver.ZFC.SitesRouting245Cut228

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.refine_228_0
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_228

example : allSites SiteRouting245.checkSite [true, true, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, true, true]) = true := refine_228_0

example : allSites SiteRouting245.checkSite [true, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, true]) = true := block_228
