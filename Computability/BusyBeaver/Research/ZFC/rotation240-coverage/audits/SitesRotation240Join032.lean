import BusyBeaver.ZFC.SitesRotation240Join032

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_512
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_513
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_514
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_515
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_516
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_517
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_518
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_519
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_520
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_521
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_522
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_523
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_524
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_525
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_526
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_527

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true]) = true := join_512

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false]) = true := join_513

example : allSites SiteRotation240.checkSite [true, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, true]) = true := join_514

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false]) = true := join_515

example : allSites SiteRotation240.checkSite [true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true]) = true := join_516

example : allSites SiteRotation240.checkSite [false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false]) = true := join_517

example : allSites SiteRotation240.checkSite [false, false, false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false, false, false]) = true := join_518

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false, false, true]) = true := join_519

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false, false]) = true := join_520

example : allSites SiteRotation240.checkSite [false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false]) = true := join_521

example : allSites SiteRotation240.checkSite [true, true, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, true, true]) = true := join_522

example : allSites SiteRotation240.checkSite [true, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, true]) = true := join_523

example : allSites SiteRotation240.checkSite [true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true]) = true := join_524

example : allSites SiteRotation240.checkSite [true, true, true]
      (descend TreeRotation240.tree [true, true, true]) = true := join_525

example : allSites SiteRotation240.checkSite [true, true]
      (descend TreeRotation240.tree [true, true]) = true := join_526

example : allSites SiteRotation240.checkSite [true]
      (descend TreeRotation240.tree [true]) = true := join_527
