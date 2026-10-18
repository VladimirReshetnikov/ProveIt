import BusyBeaver.ZFC.SitesRouting245Cut219

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.refine_219_0
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_219

example : allSites SiteRouting245.checkSite [true, false, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true]) = true := refine_219_0

example : allSites SiteRouting245.checkSite [false, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false]) = true := block_219
