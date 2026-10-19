import BusyBeaver.ZFC.SitesRotation240Join027

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_432
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_433
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_434
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_435
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_436
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_437
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_438
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_439
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_440
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_441
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_442
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_443
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_444
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_445
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_446
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_447

example : allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, true, true]) = true := join_432

example : allSites SiteRotation240.checkSite [true, true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, true]) = true := join_433

example : allSites SiteRotation240.checkSite [true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true]) = true := join_434

example : allSites SiteRotation240.checkSite [false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false]) = true := join_435

example : allSites SiteRotation240.checkSite [true, true, false, true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, false, true, true]) = true := join_436

example : allSites SiteRotation240.checkSite [true, false, true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, false, true]) = true := join_437

example : allSites SiteRotation240.checkSite [false, true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, false]) = true := join_438

example : allSites SiteRotation240.checkSite [false, true, true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, true, false]) = true := join_439

example : allSites SiteRotation240.checkSite [true, true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true, true]) = true := join_440

example : allSites SiteRotation240.checkSite [true, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, true]) = true := join_441

example : allSites SiteRotation240.checkSite [true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true]) = true := join_442

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true]) = true := join_443

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true]) = true := join_444

example : allSites SiteRotation240.checkSite [true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true]) = true := join_445

example : allSites SiteRotation240.checkSite [false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false]) = true := join_446

example : allSites SiteRotation240.checkSite [false, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, false]) = true := join_447
