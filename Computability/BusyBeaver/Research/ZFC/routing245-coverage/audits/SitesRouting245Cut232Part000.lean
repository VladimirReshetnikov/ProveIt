import BusyBeaver.ZFC.SitesRouting245Cut232Part000

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.part_232_0

example : allSites SiteRouting245.checkSite [false, false, false, false, true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true, false, false, false, false]) = true := part_232_0
