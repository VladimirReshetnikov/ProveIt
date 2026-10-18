import BusyBeaver.ZFC.SitesRouting245Cut232Part001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.part_232_1

example : allSites SiteRouting245.checkSite [true, false, false, false, true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true, false, false, false, true]) = true := part_232_1
