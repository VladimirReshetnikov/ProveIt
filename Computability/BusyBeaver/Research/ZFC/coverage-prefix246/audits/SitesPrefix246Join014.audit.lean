import BusyBeaver.ZFC.SitesPrefix246Join014

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_224
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_225
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_226
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_227
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_228
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_229
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_230
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_231

example : allSites SitePrefix246.checkSite [false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false]) = true := join_224

example : allSites SitePrefix246.checkSite [false, false, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, false, false]) = true := join_225

example : allSites SitePrefix246.checkSite [false, true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true, false]) = true := join_226

example : allSites SitePrefix246.checkSite [true, true, true, true]
      (descend ActualTree254.tree [true, true, true, true]) = true := join_227

example : allSites SitePrefix246.checkSite [true, true, true]
      (descend ActualTree254.tree [true, true, true]) = true := join_228

example : allSites SitePrefix246.checkSite [true, true]
      (descend ActualTree254.tree [true, true]) = true := join_229

example : allSites SitePrefix246.checkSite [true]
      (descend ActualTree254.tree [true]) = true := join_230

example : allSites SitePrefix246.checkSite []
      (descend ActualTree254.tree []) = true := join_231
