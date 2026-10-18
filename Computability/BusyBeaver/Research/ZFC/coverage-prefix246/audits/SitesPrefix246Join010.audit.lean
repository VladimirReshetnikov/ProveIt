import BusyBeaver.ZFC.SitesPrefix246Join010

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_160
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_161
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_162
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_163
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_164
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_165
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_166
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_167
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_168
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_169
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_170
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_171
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_172
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_173
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_174
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_175

example : allSites SitePrefix246.checkSite [true, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, true]) = true := join_160

example : allSites SitePrefix246.checkSite [true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true]) = true := join_161

example : allSites SitePrefix246.checkSite [true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true]) = true := join_162

example : allSites SitePrefix246.checkSite [false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false]) = true := join_163

example : allSites SitePrefix246.checkSite [false, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, false]) = true := join_164

example : allSites SitePrefix246.checkSite [false, true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true, false]) = true := join_165

example : allSites SitePrefix246.checkSite [true, false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false, true]) = true := join_166

example : allSites SitePrefix246.checkSite [false, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, false]) = true := join_167

example : allSites SitePrefix246.checkSite [false, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, false]) = true := join_168

example : allSites SitePrefix246.checkSite [true, true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true, true]) = true := join_169

example : allSites SitePrefix246.checkSite [true, true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true, true]) = true := join_170

example : allSites SitePrefix246.checkSite [true, true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true, true]) = true := join_171

example : allSites SitePrefix246.checkSite [true, false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false, true]) = true := join_172

example : allSites SitePrefix246.checkSite [false, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, false]) = true := join_173

example : allSites SitePrefix246.checkSite [false, false, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, false]) = true := join_174

example : allSites SitePrefix246.checkSite [true, true, false, false, true, false, true, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, true, false, true, false, false, true, true]) = true := join_175
