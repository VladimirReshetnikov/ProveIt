import BusyBeaver.ZFC.SitesRotation240Join018

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_288
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_289
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_290
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_291
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_292
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_293
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_294
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_295
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_296
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_297
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_298
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_299
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_300
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_301
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_302
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_303

example : allSites SiteRotation240.checkSite [true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true]) = true := join_288

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true]) = true := join_289

example : allSites SiteRotation240.checkSite [false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false]) = true := join_290

example : allSites SiteRotation240.checkSite [false, false, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, false, false]) = true := join_291

example : allSites SiteRotation240.checkSite [false, true, false, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, false, true, false]) = true := join_292

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, false, true]) = true := join_293

example : allSites SiteRotation240.checkSite [false, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, false]) = true := join_294

example : allSites SiteRotation240.checkSite [true, false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false, true]) = true := join_295

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true, false]) = true := join_296

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, false]) = true := join_297

example : allSites SiteRotation240.checkSite [true, true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, true, true]) = true := join_298

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true, true]) = true := join_299

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true, true]) = true := join_300

example : allSites SiteRotation240.checkSite [true, false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false, true]) = true := join_301

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, false]) = true := join_302

example : allSites SiteRotation240.checkSite [false, false, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, false, false]) = true := join_303
