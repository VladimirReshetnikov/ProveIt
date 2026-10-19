import BusyBeaver.ZFC.SitesRotation240Join006

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_96
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_97
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_98
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_99
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_100
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_101
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_102
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_103
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_104
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_105
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_106
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_107
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_108
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_109
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_110
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_111

example : allSites SiteRotation240.checkSite [false, false, false, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true, false, false, false]) = true := join_96

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true, false, false, true]) = true := join_97

example : allSites SiteRotation240.checkSite [false, false, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true, false, false]) = true := join_98

example : allSites SiteRotation240.checkSite [true, false, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true, false, true]) = true := join_99

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true, false]) = true := join_100

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true, true, false]) = true := join_101

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true, true, true]) = true := join_102

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true, true]) = true := join_103

example : allSites SiteRotation240.checkSite [true, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, true]) = true := join_104

example : allSites SiteRotation240.checkSite [false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false]) = true := join_105

example : allSites SiteRotation240.checkSite [false, false, false, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false, false, false]) = true := join_106

example : allSites SiteRotation240.checkSite [false, false, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false, false]) = true := join_107

example : allSites SiteRotation240.checkSite [true, false, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false, true]) = true := join_108

example : allSites SiteRotation240.checkSite [false, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, false]) = true := join_109

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, false]) = true := join_110

example : allSites SiteRotation240.checkSite [false, false, false, true, false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true, false, false, false]) = true := join_111
