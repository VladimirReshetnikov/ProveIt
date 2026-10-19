import BusyBeaver.ZFC.SitesRotation240Join029

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_464
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_465
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_466
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_467
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_468
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_469
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_470
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_471
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_472
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_473
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_474
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_475
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_476
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_477
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_478
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_479

example : allSites SiteRotation240.checkSite [true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true]) = true := join_464

example : allSites SiteRotation240.checkSite [true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true]) = true := join_465

example : allSites SiteRotation240.checkSite [true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true]) = true := join_466

example : allSites SiteRotation240.checkSite [true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true]) = true := join_467

example : allSites SiteRotation240.checkSite [true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true]) = true := join_468

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false]) = true := join_469

example : allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false]) = true := join_470

example : allSites SiteRotation240.checkSite [true, true, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true]) = true := join_471

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true]) = true := join_472

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false]) = true := join_473

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false]) = true := join_474

example : allSites SiteRotation240.checkSite [true, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true]) = true := join_475

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false]) = true := join_476

example : allSites SiteRotation240.checkSite [true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true]) = true := join_477

example : allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false]) = true := join_478

example : allSites SiteRotation240.checkSite [false, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false]) = true := join_479
