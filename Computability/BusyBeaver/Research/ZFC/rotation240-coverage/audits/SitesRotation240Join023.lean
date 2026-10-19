import BusyBeaver.ZFC.SitesRotation240Join023

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_368
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_369
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_370
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_371
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_372
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_373
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_374
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_375
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_376
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_377
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_378
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_379
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_380
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_381
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_382
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_383

example : allSites SiteRotation240.checkSite [true, true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true, true]) = true := join_368

example : allSites SiteRotation240.checkSite [true, true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true, true]) = true := join_369

example : allSites SiteRotation240.checkSite [true, true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true, true]) = true := join_370

example : allSites SiteRotation240.checkSite [true, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, true]) = true := join_371

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true]) = true := join_372

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true]) = true := join_373

example : allSites SiteRotation240.checkSite [true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true]) = true := join_374

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false]) = true := join_375

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false]) = true := join_376

example : allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, true, true, false]) = true := join_377

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, true, true]) = true := join_378

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, true]) = true := join_379

example : allSites SiteRotation240.checkSite [true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true]) = true := join_380

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false]) = true := join_381

example : allSites SiteRotation240.checkSite [false, false, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, false, false]) = true := join_382

example : allSites SiteRotation240.checkSite [false, true, false, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, false, true, false]) = true := join_383
