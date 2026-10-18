import BusyBeaver.ZFC.SitesRouting245Cut209

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.refine_209_0
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_209

example : allSites SiteRouting245.checkSite [true, true, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true]) = true := refine_209_0

example : allSites SiteRouting245.checkSite [true, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true]) = true := block_209
