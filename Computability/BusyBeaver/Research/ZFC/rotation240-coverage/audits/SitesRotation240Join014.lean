import BusyBeaver.ZFC.SitesRotation240Join014

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_224
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_225
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_226
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_227
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_228
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_229
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_230
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_231
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_232
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_233
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_234
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_235
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_236
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_237
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_238
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_239

example : allSites SiteRotation240.checkSite [false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false]) = true := join_224

example : allSites SiteRotation240.checkSite [false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, false]) = true := join_225

example : allSites SiteRotation240.checkSite [false, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false]) = true := join_226

example : allSites SiteRotation240.checkSite [false, true, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false]) = true := join_227

example : allSites SiteRotation240.checkSite [true, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true]) = true := join_228

example : allSites SiteRotation240.checkSite [true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true]) = true := join_229

example : allSites SiteRotation240.checkSite [false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false]) = true := join_230

example : allSites SiteRotation240.checkSite [false, true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, false]) = true := join_231

example : allSites SiteRotation240.checkSite [false, true, true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false]) = true := join_232

example : allSites SiteRotation240.checkSite [true, true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, true]) = true := join_233

example : allSites SiteRotation240.checkSite [true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true]) = true := join_234

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false]) = true := join_235

example : allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, false]) = true := join_236

example : allSites SiteRotation240.checkSite [true, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, true]) = true := join_237

example : allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false]) = true := join_238

example : allSites SiteRotation240.checkSite [false, true, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, true, false]) = true := join_239
