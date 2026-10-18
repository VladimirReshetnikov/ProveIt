import BusyBeaver.ZFC.SitesRouting245Cut230Part001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.part_230_1

example : allSites SiteRouting245.checkSite [true, true, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, true, true]) = true := part_230_1
