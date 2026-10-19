import BusyBeaver.ZFC.SitesRotation240Join025

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_400
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_401
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_402
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_403
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_404
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_405
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_406
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_407
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_408
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_409
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_410
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_411
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_412
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_413
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_414
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_415

example : allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, true, false]) = true := join_400

example : allSites SiteRotation240.checkSite [true, true, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, true, true, true]) = true := join_401

example : allSites SiteRotation240.checkSite [true, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, true, true]) = true := join_402

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, true]) = true := join_403

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true]) = true := join_404

example : allSites SiteRotation240.checkSite [true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true]) = true := join_405

example : allSites SiteRotation240.checkSite [false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false]) = true := join_406

example : allSites SiteRotation240.checkSite [false, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, false]) = true := join_407

example : allSites SiteRotation240.checkSite [false, true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true, false]) = true := join_408

example : allSites SiteRotation240.checkSite [true, false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false, true]) = true := join_409

example : allSites SiteRotation240.checkSite [false, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false]) = true := join_410

example : allSites SiteRotation240.checkSite [true, false, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, false, true]) = true := join_411

example : allSites SiteRotation240.checkSite [false, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, false]) = true := join_412

example : allSites SiteRotation240.checkSite [false, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true, false]) = true := join_413

example : allSites SiteRotation240.checkSite [true, true, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true, true, true]) = true := join_414

example : allSites SiteRotation240.checkSite [true, true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true, true]) = true := join_415
