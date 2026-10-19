import BusyBeaver.ZFC.SitesRotation240Join022

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_352
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_353
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_354
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_355
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_356
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_357
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_358
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_359
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_360
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_361
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_362
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_363
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_364
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_365
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_366
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_367

example : allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, true]) = true := join_352

example : allSites SiteRotation240.checkSite [true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true]) = true := join_353

example : allSites SiteRotation240.checkSite [true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true]) = true := join_354

example : allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false]) = true := join_355

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, false, true]) = true := join_356

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, false]) = true := join_357

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true, false]) = true := join_358

example : allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true, true, true]) = true := join_359

example : allSites SiteRotation240.checkSite [true, true, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true, true]) = true := join_360

example : allSites SiteRotation240.checkSite [true, false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false, true]) = true := join_361

example : allSites SiteRotation240.checkSite [false, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, false]) = true := join_362

example : allSites SiteRotation240.checkSite [true, false, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, false, true]) = true := join_363

example : allSites SiteRotation240.checkSite [false, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, false]) = true := join_364

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, false, false]) = true := join_365

example : allSites SiteRotation240.checkSite [false, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, false]) = true := join_366

example : allSites SiteRotation240.checkSite [true, true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, true, true]) = true := join_367
