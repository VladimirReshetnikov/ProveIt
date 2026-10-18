import BusyBeaver.ZFC.SitesRouting245Cut234

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_234

example : allSites SiteRouting245.checkSite [true, false, true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true, false, true]) = true := block_234
