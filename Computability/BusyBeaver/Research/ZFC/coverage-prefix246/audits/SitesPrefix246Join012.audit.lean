import BusyBeaver.ZFC.SitesPrefix246Join012

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_192
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_193
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_194
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_195
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_196
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_197
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_198
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_199
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_200
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_201
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_202
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_203
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_204
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_205
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_206
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_207

example : allSites SitePrefix246.checkSite [false, false, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false, false]) = true := join_192

example : allSites SitePrefix246.checkSite [false, true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true, false]) = true := join_193

example : allSites SitePrefix246.checkSite [true, true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true, true]) = true := join_194

example : allSites SitePrefix246.checkSite [true, false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false, true]) = true := join_195

example : allSites SitePrefix246.checkSite [false, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, false]) = true := join_196

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false, false]) = true := join_197

example : allSites SitePrefix246.checkSite [false, true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true, false]) = true := join_198

example : allSites SitePrefix246.checkSite [true, false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false, true]) = true := join_199

example : allSites SitePrefix246.checkSite [false, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, false]) = true := join_200

example : allSites SitePrefix246.checkSite [false, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, false]) = true := join_201

example : allSites SitePrefix246.checkSite [true, true, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true, true]) = true := join_202

example : allSites SitePrefix246.checkSite [true, true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true, true]) = true := join_203

example : allSites SitePrefix246.checkSite [true, false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false, true]) = true := join_204

example : allSites SitePrefix246.checkSite [false, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, false]) = true := join_205

example : allSites SitePrefix246.checkSite [true, false, false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false, true]) = true := join_206

example : allSites SitePrefix246.checkSite [false, false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false, false]) = true := join_207
