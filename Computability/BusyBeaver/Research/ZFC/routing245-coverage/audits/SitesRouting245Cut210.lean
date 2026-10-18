import BusyBeaver.ZFC.SitesRouting245Cut210

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.refine_210_0
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_210

example : allSites SiteRouting245.checkSite [false, true, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false]) = true := refine_210_0

example : allSites SiteRouting245.checkSite [true, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true]) = true := block_210
