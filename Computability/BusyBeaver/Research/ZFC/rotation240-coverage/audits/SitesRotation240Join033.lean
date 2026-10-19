import BusyBeaver.ZFC.SitesRotation240Join033

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_528

example : allSites SiteRotation240.checkSite []
      (descend TreeRotation240.tree []) = true := join_528
