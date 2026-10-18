import BusyBeaver.ZFC.SitesPrefix246Join007

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_112
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_113
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_114
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_115
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_116
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_117
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_118
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_119
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_120
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_121
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_122
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_123
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_124
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_125
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_126
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_127

example : allSites SitePrefix246.checkSite [false, false, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false, false]) = true := join_112

example : allSites SitePrefix246.checkSite [false, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false]) = true := join_113

example : allSites SitePrefix246.checkSite [true, false, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, true]) = true := join_114

example : allSites SitePrefix246.checkSite [false, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false]) = true := join_115

example : allSites SitePrefix246.checkSite [true, true, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true]) = true := join_116

example : allSites SitePrefix246.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true]) = true := join_117

example : allSites SitePrefix246.checkSite [false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false]) = true := join_118

example : allSites SitePrefix246.checkSite [true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true]) = true := join_119

example : allSites SitePrefix246.checkSite [true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true]) = true := join_120

example : allSites SitePrefix246.checkSite [false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false]) = true := join_121

example : allSites SitePrefix246.checkSite [true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true]) = true := join_122

example : allSites SitePrefix246.checkSite [false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false]) = true := join_123

example : allSites SitePrefix246.checkSite [false, true, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false]) = true := join_124

example : allSites SitePrefix246.checkSite [true, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true]) = true := join_125

example : allSites SitePrefix246.checkSite [false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false]) = true := join_126

example : allSites SitePrefix246.checkSite [false, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false]) = true := join_127
