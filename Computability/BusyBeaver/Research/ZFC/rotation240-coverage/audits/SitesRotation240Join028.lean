import BusyBeaver.ZFC.SitesRotation240Join028

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_448
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_449
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_450
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_451
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_452
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_453
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_454
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_455
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_456
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_457
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_458
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_459
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_460
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_461
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_462
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_463

example : allSites SiteRotation240.checkSite [true, true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true]) = true := join_448

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true]) = true := join_449

example : allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false]) = true := join_450

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false]) = true := join_451

example : allSites SiteRotation240.checkSite [true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true]) = true := join_452

example : allSites SiteRotation240.checkSite [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false]) = true := join_453

example : allSites SiteRotation240.checkSite [false, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false]) = true := join_454

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false]) = true := join_455

example : allSites SiteRotation240.checkSite [true, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true]) = true := join_456

example : allSites SiteRotation240.checkSite [false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false]) = true := join_457

example : allSites SiteRotation240.checkSite [true, true, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true]) = true := join_458

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true]) = true := join_459

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false]) = true := join_460

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false]) = true := join_461

example : allSites SiteRotation240.checkSite [true, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true]) = true := join_462

example : allSites SiteRotation240.checkSite [false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false]) = true := join_463
