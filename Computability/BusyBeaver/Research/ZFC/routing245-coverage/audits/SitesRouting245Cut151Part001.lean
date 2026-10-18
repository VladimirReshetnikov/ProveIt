import BusyBeaver.ZFC.SitesRouting245Cut151Part001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.part_151_1

example : allSites SiteRouting245.checkSite [false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false]) = true := part_151_1
