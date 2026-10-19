import BusyBeaver.ZFC.SitesRotation240Join026

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_416
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_417
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_418
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_419
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_420
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_421
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_422
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_423
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_424
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_425
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_426
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_427
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_428
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_429
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_430
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_431

example : allSites SiteRotation240.checkSite [true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true]) = true := join_416

example : allSites SiteRotation240.checkSite [true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true]) = true := join_417

example : allSites SiteRotation240.checkSite [true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true]) = true := join_418

example : allSites SiteRotation240.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true]) = true := join_419

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false]) = true := join_420

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false, true]) = true := join_421

example : allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false]) = true := join_422

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false, false]) = true := join_423

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false]) = true := join_424

example : allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, true, true]) = true := join_425

example : allSites SiteRotation240.checkSite [true, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, true]) = true := join_426

example : allSites SiteRotation240.checkSite [true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true]) = true := join_427

example : allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false]) = true := join_428

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, true]) = true := join_429

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false]) = true := join_430

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, false]) = true := join_431
