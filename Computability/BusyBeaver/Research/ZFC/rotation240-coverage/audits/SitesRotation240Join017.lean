import BusyBeaver.ZFC.SitesRotation240Join017

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_272
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_273
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_274
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_275
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_276
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_277
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_278
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_279
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_280
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_281
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_282
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_283
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_284
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_285
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_286
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_287

example : allSites SiteRotation240.checkSite [true, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, true]) = true := join_272

example : allSites SiteRotation240.checkSite [true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true]) = true := join_273

example : allSites SiteRotation240.checkSite [false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false]) = true := join_274

example : allSites SiteRotation240.checkSite [false, false, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, false, false]) = true := join_275

example : allSites SiteRotation240.checkSite [false, true, false, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, false, true, false]) = true := join_276

example : allSites SiteRotation240.checkSite [false, true, true, false, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, false, true, true, false]) = true := join_277

example : allSites SiteRotation240.checkSite [true, true, false, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, false, true, true]) = true := join_278

example : allSites SiteRotation240.checkSite [true, false, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, false, true]) = true := join_279

example : allSites SiteRotation240.checkSite [false, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, false]) = true := join_280

example : allSites SiteRotation240.checkSite [false, false, false, true, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, false, false, false]) = true := join_281

example : allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, false, false]) = true := join_282

example : allSites SiteRotation240.checkSite [false, true, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, false]) = true := join_283

example : allSites SiteRotation240.checkSite [false, true, true, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, true, false]) = true := join_284

example : allSites SiteRotation240.checkSite [true, true, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true, true]) = true := join_285

example : allSites SiteRotation240.checkSite [true, true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true, true]) = true := join_286

example : allSites SiteRotation240.checkSite [true, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, true]) = true := join_287
