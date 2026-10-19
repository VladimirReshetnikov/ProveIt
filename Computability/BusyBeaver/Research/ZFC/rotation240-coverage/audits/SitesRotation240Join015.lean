import BusyBeaver.ZFC.SitesRotation240Join015

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_240
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_241
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_242
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_243
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_244
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_245
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_246
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_247
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_248
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_249
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_250
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_251
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_252
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_253
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_254
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_255

example : allSites SiteRotation240.checkSite [true, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, true]) = true := join_240

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true]) = true := join_241

example : allSites SiteRotation240.checkSite [true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true]) = true := join_242

example : allSites SiteRotation240.checkSite [true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true]) = true := join_243

example : allSites SiteRotation240.checkSite [false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false]) = true := join_244

example : allSites SiteRotation240.checkSite [false, false, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, false, false]) = true := join_245

example : allSites SiteRotation240.checkSite [true, false, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, false, true]) = true := join_246

example : allSites SiteRotation240.checkSite [false, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, false]) = true := join_247

example : allSites SiteRotation240.checkSite [false, false, false, true, false, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false, true, false, false, false]) = true := join_248

example : allSites SiteRotation240.checkSite [false, false, true, false, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false, true, false, false]) = true := join_249

example : allSites SiteRotation240.checkSite [false, true, false, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false, true, false]) = true := join_250

example : allSites SiteRotation240.checkSite [false, true, true, false, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false, true, true, false]) = true := join_251

example : allSites SiteRotation240.checkSite [true, true, false, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false, true, true]) = true := join_252

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false, true]) = true := join_253

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false]) = true := join_254

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, false, true]) = true := join_255
