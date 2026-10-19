import BusyBeaver.ZFC.SitesRotation240Join019

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_304
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_305
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_306
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_307
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_308
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_309
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_310
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_311
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_312
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_313
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_314
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_315
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_316
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_317
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_318
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_319

example : allSites SiteRotation240.checkSite [true, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, false, true]) = true := join_304

example : allSites SiteRotation240.checkSite [false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, false]) = true := join_305

example : allSites SiteRotation240.checkSite [false, false, false, true, false, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, false, true, false, false, false]) = true := join_306

example : allSites SiteRotation240.checkSite [false, false, true, false, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, false, true, false, false]) = true := join_307

example : allSites SiteRotation240.checkSite [false, true, false, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, false, true, false]) = true := join_308

example : allSites SiteRotation240.checkSite [false, true, true, false, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, false, true, true, false]) = true := join_309

example : allSites SiteRotation240.checkSite [true, true, false, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, false, true, true]) = true := join_310

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, false, true]) = true := join_311

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, false]) = true := join_312

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true]) = true := join_313

example : allSites SiteRotation240.checkSite [false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false]) = true := join_314

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false]) = true := join_315

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, true]) = true := join_316

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true]) = true := join_317

example : allSites SiteRotation240.checkSite [true, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true]) = true := join_318

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false]) = true := join_319
