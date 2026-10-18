import BusyBeaver.ZFC.SitesRouting245Cut232

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.block_232

example : allSites SiteRouting245.checkSite [false, false, false, true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true, false, false, false]) = true := block_232
