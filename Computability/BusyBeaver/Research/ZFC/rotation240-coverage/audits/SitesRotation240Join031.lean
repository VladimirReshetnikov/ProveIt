import BusyBeaver.ZFC.SitesRotation240Join031

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_496
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_497
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_498
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_499
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_500
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_501
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_502
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_503
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_504
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_505
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_506
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_507
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_508
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_509
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_510
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_511

example : allSites SiteRotation240.checkSite [false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false]) = true := join_496

example : allSites SiteRotation240.checkSite [true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true]) = true := join_497

example : allSites SiteRotation240.checkSite [true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true]) = true := join_498

example : allSites SiteRotation240.checkSite [true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true]) = true := join_499

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true]) = true := join_500

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true]) = true := join_501

example : allSites SiteRotation240.checkSite [true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true]) = true := join_502

example : allSites SiteRotation240.checkSite [false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false]) = true := join_503

example : allSites SiteRotation240.checkSite [true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true]) = true := join_504

example : allSites SiteRotation240.checkSite [true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true]) = true := join_505

example : allSites SiteRotation240.checkSite [false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false]) = true := join_506

example : allSites SiteRotation240.checkSite [true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true]) = true := join_507

example : allSites SiteRotation240.checkSite [false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false]) = true := join_508

example : allSites SiteRotation240.checkSite [true, true, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true]) = true := join_509

example : allSites SiteRotation240.checkSite [true, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true]) = true := join_510

example : allSites SiteRotation240.checkSite [false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false]) = true := join_511
