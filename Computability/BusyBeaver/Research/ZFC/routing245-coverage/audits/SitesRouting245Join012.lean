import BusyBeaver.ZFC.SitesRouting245Join012

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_192
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_193
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_194
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_195
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_196
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_197
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_198
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_199
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_200
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_201
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_202
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_203
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_204
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_205
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_206
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_207

example : allSites SiteRouting245.checkSite [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false]) = true := join_192

example : allSites SiteRouting245.checkSite [false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false]) = true := join_193

example : allSites SiteRouting245.checkSite [false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false]) = true := join_194

example : allSites SiteRouting245.checkSite [false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false]) = true := join_195

example : allSites SiteRouting245.checkSite [true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true]) = true := join_196

example : allSites SiteRouting245.checkSite [true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true]) = true := join_197

example : allSites SiteRouting245.checkSite [true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true]) = true := join_198

example : allSites SiteRouting245.checkSite [true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true]) = true := join_199

example : allSites SiteRouting245.checkSite [true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true]) = true := join_200

example : allSites SiteRouting245.checkSite [false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false]) = true := join_201

example : allSites SiteRouting245.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false]) = true := join_202

example : allSites SiteRouting245.checkSite [false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false]) = true := join_203

example : allSites SiteRouting245.checkSite [true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true]) = true := join_204

example : allSites SiteRouting245.checkSite [false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false]) = true := join_205

example : allSites SiteRouting245.checkSite [false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false]) = true := join_206

example : allSites SiteRouting245.checkSite [true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true]) = true := join_207
