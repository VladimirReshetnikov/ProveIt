import BusyBeaver.ZFC.SitesRotation240Batch000

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.block_0

example : allSites SiteRotation240.checkSite [false]
      (descend TreeRotation240.tree [false]) = true := block_0
