import BusyBeaver.ZFC.SitesRotation240Join030

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_480
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_481
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_482
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_483
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_484
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_485
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_486
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_487
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_488
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_489
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_490
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_491
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_492
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_493
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_494
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_495

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false]) = true := join_480

example : allSites SiteRotation240.checkSite [true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true]) = true := join_481

example : allSites SiteRotation240.checkSite [false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false]) = true := join_482

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true]) = true := join_483

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false]) = true := join_484

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false]) = true := join_485

example : allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true]) = true := join_486

example : allSites SiteRotation240.checkSite [true, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true]) = true := join_487

example : allSites SiteRotation240.checkSite [true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true]) = true := join_488

example : allSites SiteRotation240.checkSite [false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false]) = true := join_489

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true]) = true := join_490

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false]) = true := join_491

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false]) = true := join_492

example : allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true]) = true := join_493

example : allSites SiteRotation240.checkSite [true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true]) = true := join_494

example : allSites SiteRotation240.checkSite [true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true]) = true := join_495
