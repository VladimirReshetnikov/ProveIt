import BusyBeaver.ZFC.SitesPrefix246Join013

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_208
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_209
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_210
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_211
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_212
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_213
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_214
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_215
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_216
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_217
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_218
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_219
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_220
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_221
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_222
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_223

example : allSites SitePrefix246.checkSite [false, true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true, false]) = true := join_208

example : allSites SitePrefix246.checkSite [true, true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true, true]) = true := join_209

example : allSites SitePrefix246.checkSite [true, true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true, true]) = true := join_210

example : allSites SitePrefix246.checkSite [true, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, true]) = true := join_211

example : allSites SitePrefix246.checkSite [true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true]) = true := join_212

example : allSites SitePrefix246.checkSite [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]) = true := join_213

example : allSites SitePrefix246.checkSite [true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true]) = true := join_214

example : allSites SitePrefix246.checkSite [true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true]) = true := join_215

example : allSites SitePrefix246.checkSite [false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false]) = true := join_216

example : allSites SitePrefix246.checkSite [true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true]) = true := join_217

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false]) = true := join_218

example : allSites SitePrefix246.checkSite [false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false]) = true := join_219

example : allSites SitePrefix246.checkSite [true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true]) = true := join_220

example : allSites SitePrefix246.checkSite [false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false]) = true := join_221

example : allSites SitePrefix246.checkSite [false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false]) = true := join_222

example : allSites SitePrefix246.checkSite [true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true]) = true := join_223
