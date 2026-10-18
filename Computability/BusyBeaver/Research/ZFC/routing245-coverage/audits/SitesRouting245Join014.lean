import BusyBeaver.ZFC.SitesRouting245Join014

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_224
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_225
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_226
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_227
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_228
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_229
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_230
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_231
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_232
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_233
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_234

example : allSites SiteRouting245.checkSite [false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false]) = true := join_224

example : allSites SiteRouting245.checkSite [false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false]) = true := join_225

example : allSites SiteRouting245.checkSite [true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true]) = true := join_226

example : allSites SiteRouting245.checkSite [false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false]) = true := join_227

example : allSites SiteRouting245.checkSite [false, false, true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true, false, false]) = true := join_228

example : allSites SiteRouting245.checkSite [false, true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true, false]) = true := join_229

example : allSites SiteRouting245.checkSite [true, true, true, true]
      (descend TreeRouting245.tree [true, true, true, true]) = true := join_230

example : allSites SiteRouting245.checkSite [true, true, true]
      (descend TreeRouting245.tree [true, true, true]) = true := join_231

example : allSites SiteRouting245.checkSite [true, true]
      (descend TreeRouting245.tree [true, true]) = true := join_232

example : allSites SiteRouting245.checkSite [true]
      (descend TreeRouting245.tree [true]) = true := join_233

example : allSites SiteRouting245.checkSite []
      (descend TreeRouting245.tree []) = true := join_234
