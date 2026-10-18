import BusyBeaver.ZFC.SitesPrefix246Join009

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_144
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_145
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_146
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_147
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_148
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_149
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_150
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_151
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_152
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_153
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_154
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_155
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_156
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_157
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_158
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_159

example : allSites SitePrefix246.checkSite [false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false]) = true := join_144

example : allSites SitePrefix246.checkSite [false, true, false, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, false, true, false]) = true := join_145

example : allSites SitePrefix246.checkSite [true, false, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, false, true]) = true := join_146

example : allSites SitePrefix246.checkSite [false, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, false]) = true := join_147

example : allSites SitePrefix246.checkSite [false, false, true, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, true, false, false]) = true := join_148

example : allSites SitePrefix246.checkSite [true, false, true, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, true, false, true]) = true := join_149

example : allSites SitePrefix246.checkSite [false, true, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, true, false]) = true := join_150

example : allSites SitePrefix246.checkSite [false, true, true, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, true, true, false]) = true := join_151

example : allSites SitePrefix246.checkSite [true, true, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, true, true]) = true := join_152

example : allSites SitePrefix246.checkSite [true, false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false, true]) = true := join_153

example : allSites SitePrefix246.checkSite [false, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, false]) = true := join_154

example : allSites SitePrefix246.checkSite [true, false, false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, false, true]) = true := join_155

example : allSites SitePrefix246.checkSite [false, false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, false]) = true := join_156

example : allSites SitePrefix246.checkSite [true, true, false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, true, true]) = true := join_157

example : allSites SitePrefix246.checkSite [true, false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false, true]) = true := join_158

example : allSites SitePrefix246.checkSite [false, true, true, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, true, true, false]) = true := join_159
