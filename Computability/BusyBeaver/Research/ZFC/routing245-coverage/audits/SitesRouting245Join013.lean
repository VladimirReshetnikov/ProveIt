import BusyBeaver.ZFC.SitesRouting245Join013

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_208
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_209
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_210
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_211
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_212
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_213
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_214
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_215
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_216
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_217
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_218
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_219
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_220
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_221
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_222
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_223

example : allSites SiteRouting245.checkSite [false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false]) = true := join_208

example : allSites SiteRouting245.checkSite [true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true]) = true := join_209

example : allSites SiteRouting245.checkSite [false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false]) = true := join_210

example : allSites SiteRouting245.checkSite [true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true]) = true := join_211

example : allSites SiteRouting245.checkSite [true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true]) = true := join_212

example : allSites SiteRouting245.checkSite [true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true]) = true := join_213

example : allSites SiteRouting245.checkSite [true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true]) = true := join_214

example : allSites SiteRouting245.checkSite [true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true]) = true := join_215

example : allSites SiteRouting245.checkSite [true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true]) = true := join_216

example : allSites SiteRouting245.checkSite [false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false]) = true := join_217

example : allSites SiteRouting245.checkSite [true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true]) = true := join_218

example : allSites SiteRouting245.checkSite [false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false]) = true := join_219

example : allSites SiteRouting245.checkSite [true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true]) = true := join_220

example : allSites SiteRouting245.checkSite [false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false]) = true := join_221

example : allSites SiteRouting245.checkSite [false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false]) = true := join_222

example : allSites SiteRouting245.checkSite [true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true]) = true := join_223
