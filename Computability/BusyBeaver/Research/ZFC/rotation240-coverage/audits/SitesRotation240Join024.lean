import BusyBeaver.ZFC.SitesRotation240Join024

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_384
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_385
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_386
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_387
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_388
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_389
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_390
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_391
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_392
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_393
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_394
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_395
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_396
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_397
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_398
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_399

example : allSites SiteRotation240.checkSite [true, false, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, false, true]) = true := join_384

example : allSites SiteRotation240.checkSite [false, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, false]) = true := join_385

example : allSites SiteRotation240.checkSite [false, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, false]) = true := join_386

example : allSites SiteRotation240.checkSite [false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false]) = true := join_387

example : allSites SiteRotation240.checkSite [true, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, true, false, true]) = true := join_388

example : allSites SiteRotation240.checkSite [false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, true, false]) = true := join_389

example : allSites SiteRotation240.checkSite [false, true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, true, true, false]) = true := join_390

example : allSites SiteRotation240.checkSite [true, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, true, true]) = true := join_391

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false, true]) = true := join_392

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, false]) = true := join_393

example : allSites SiteRotation240.checkSite [false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false]) = true := join_394

example : allSites SiteRotation240.checkSite [true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true]) = true := join_395

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false]) = true := join_396

example : allSites SiteRotation240.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true]) = true := join_397

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, false]) = true := join_398

example : allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, true, false, false]) = true := join_399
