import BusyBeaver.ZFC.SitesRouting245Cut230Part000

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.part_230_0

example : allSites SiteRouting245.checkSite [false, true, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, true, false]) = true := part_230_0
