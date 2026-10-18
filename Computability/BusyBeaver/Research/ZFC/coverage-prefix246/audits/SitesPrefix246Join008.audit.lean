import BusyBeaver.ZFC.SitesPrefix246Join008

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_128
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_129
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_130
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_131
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_132
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_133
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_134
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_135
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_136
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_137
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_138
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_139
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_140
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_141
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_142
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_143

example : allSites SitePrefix246.checkSite [true, true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true, true]) = true := join_128

example : allSites SitePrefix246.checkSite [true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true]) = true := join_129

example : allSites SitePrefix246.checkSite [true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true]) = true := join_130

example : allSites SitePrefix246.checkSite [true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true]) = true := join_131

example : allSites SitePrefix246.checkSite [true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true]) = true := join_132

example : allSites SitePrefix246.checkSite [false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false]) = true := join_133

example : allSites SitePrefix246.checkSite [false, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, false]) = true := join_134

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, false]) = true := join_135

example : allSites SitePrefix246.checkSite [false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false]) = true := join_136

example : allSites SitePrefix246.checkSite [true, false, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false, true]) = true := join_137

example : allSites SitePrefix246.checkSite [false, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false]) = true := join_138

example : allSites SitePrefix246.checkSite [true, true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, true]) = true := join_139

example : allSites SitePrefix246.checkSite [true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true]) = true := join_140

example : allSites SitePrefix246.checkSite [false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false]) = true := join_141

example : allSites SitePrefix246.checkSite [true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true]) = true := join_142

example : allSites SitePrefix246.checkSite [true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true]) = true := join_143
