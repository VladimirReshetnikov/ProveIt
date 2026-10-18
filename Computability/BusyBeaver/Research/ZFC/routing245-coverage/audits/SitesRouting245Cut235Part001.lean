import BusyBeaver.ZFC.SitesRouting245Cut235Part001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.part_235_1

example : allSites SiteRouting245.checkSite [false, true, true, true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true, true, true, false]) = true := part_235_1
