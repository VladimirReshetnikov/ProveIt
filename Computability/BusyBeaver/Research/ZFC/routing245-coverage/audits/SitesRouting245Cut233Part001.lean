import BusyBeaver.ZFC.SitesRouting245Cut233Part001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.part_233_1

example : allSites SiteRouting245.checkSite [true, true, false, false, true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true, false, false, true, true]) = true := part_233_1
