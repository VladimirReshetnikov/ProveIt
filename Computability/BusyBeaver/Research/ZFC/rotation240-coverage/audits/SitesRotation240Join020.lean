import BusyBeaver.ZFC.SitesRotation240Join020

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_320
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_321
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_322
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_323
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_324
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_325
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_326
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_327
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_328
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_329
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_330
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_331
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_332
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_333
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_334
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_335

example : allSites SiteRotation240.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true]) = true := join_320

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false]) = true := join_321

example : allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false]) = true := join_322

example : allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, true, false]) = true := join_323

example : allSites SiteRotation240.checkSite [true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true]) = true := join_324

example : allSites SiteRotation240.checkSite [true, true, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, true, true]) = true := join_325

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, true]) = true := join_326

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true]) = true := join_327

example : allSites SiteRotation240.checkSite [true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true]) = true := join_328

example : allSites SiteRotation240.checkSite [false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false]) = true := join_329

example : allSites SiteRotation240.checkSite [true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, true]) = true := join_330

example : allSites SiteRotation240.checkSite [true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true]) = true := join_331

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false]) = true := join_332

example : allSites SiteRotation240.checkSite [false, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, false]) = true := join_333

example : allSites SiteRotation240.checkSite [true, true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, true, true]) = true := join_334

example : allSites SiteRotation240.checkSite [true, false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false, true]) = true := join_335
