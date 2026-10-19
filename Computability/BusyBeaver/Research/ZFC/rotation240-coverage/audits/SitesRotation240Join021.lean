import BusyBeaver.ZFC.SitesRotation240Join021

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_336
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_337
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_338
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_339
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_340
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_341
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_342
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_343
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_344
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_345
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_346
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_347
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_348
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_349
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_350
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_351

example : allSites SiteRotation240.checkSite [false, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true, false]) = true := join_336

example : allSites SiteRotation240.checkSite [false, true, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true, true, false]) = true := join_337

example : allSites SiteRotation240.checkSite [true, true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true, true]) = true := join_338

example : allSites SiteRotation240.checkSite [true, false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false, true]) = true := join_339

example : allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, false]) = true := join_340

example : allSites SiteRotation240.checkSite [false, false, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, false, false]) = true := join_341

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, false, true]) = true := join_342

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, false]) = true := join_343

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true, false]) = true := join_344

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true, true]) = true := join_345

example : allSites SiteRotation240.checkSite [true, false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false, true]) = true := join_346

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, false]) = true := join_347

example : allSites SiteRotation240.checkSite [false, false, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, false, false]) = true := join_348

example : allSites SiteRotation240.checkSite [true, false, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, false, true]) = true := join_349

example : allSites SiteRotation240.checkSite [false, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, false]) = true := join_350

example : allSites SiteRotation240.checkSite [false, true, true, true, false, true, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, true, false, true, true, true, false]) = true := join_351
