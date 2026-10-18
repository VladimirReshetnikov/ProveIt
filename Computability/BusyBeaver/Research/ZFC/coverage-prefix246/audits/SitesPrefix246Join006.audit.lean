import BusyBeaver.ZFC.SitesPrefix246Join006

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_96
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_97
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_98
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_99
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_100
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_101
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_102
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_103
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_104
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_105
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_106
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_107
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_108
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_109
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_110
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_111

example : allSites SitePrefix246.checkSite [false, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, false]) = true := join_96

example : allSites SitePrefix246.checkSite [true, false, false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false, true]) = true := join_97

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, false]) = true := join_98

example : allSites SitePrefix246.checkSite [false, true, false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, true, false]) = true := join_99

example : allSites SitePrefix246.checkSite [true, false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false, true]) = true := join_100

example : allSites SitePrefix246.checkSite [false, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, false]) = true := join_101

example : allSites SitePrefix246.checkSite [true, false, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false, true]) = true := join_102

example : allSites SitePrefix246.checkSite [false, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, false]) = true := join_103

example : allSites SitePrefix246.checkSite [false, true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true, false]) = true := join_104

example : allSites SitePrefix246.checkSite [false, true, true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true, true, false]) = true := join_105

example : allSites SitePrefix246.checkSite [true, true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true, true]) = true := join_106

example : allSites SitePrefix246.checkSite [true, true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true, true]) = true := join_107

example : allSites SitePrefix246.checkSite [true, true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true, true]) = true := join_108

example : allSites SitePrefix246.checkSite [true, false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false, true]) = true := join_109

example : allSites SitePrefix246.checkSite [false, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false]) = true := join_110

example : allSites SitePrefix246.checkSite [false, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, false]) = true := join_111
