import BusyBeaver.ZFC.SitesRotation240Join005

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_80
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_81
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_82
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_83
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_84
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_85
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_86
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_87
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_88
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_89
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_90
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_91
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_92
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_93
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_94
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_95

example : allSites SiteRotation240.checkSite [false, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, false]) = true := join_80

example : allSites SiteRotation240.checkSite [false, false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true, false, false, false]) = true := join_81

example : allSites SiteRotation240.checkSite [false, false, true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true, false, false]) = true := join_82

example : allSites SiteRotation240.checkSite [false, true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true, false]) = true := join_83

example : allSites SiteRotation240.checkSite [false, true, true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true, true, false]) = true := join_84

example : allSites SiteRotation240.checkSite [true, true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true, true]) = true := join_85

example : allSites SiteRotation240.checkSite [true, true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true, true]) = true := join_86

example : allSites SiteRotation240.checkSite [true, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, true]) = true := join_87

example : allSites SiteRotation240.checkSite [true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true]) = true := join_88

example : allSites SiteRotation240.checkSite [false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false]) = true := join_89

example : allSites SiteRotation240.checkSite [true, true, false, false, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, false, false, true, true]) = true := join_90

example : allSites SiteRotation240.checkSite [true, false, false, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, false, false, true]) = true := join_91

example : allSites SiteRotation240.checkSite [false, false, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, false, false]) = true := join_92

example : allSites SiteRotation240.checkSite [false, true, false, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, false, true, false]) = true := join_93

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, false, true]) = true := join_94

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, false, false]) = true := join_95
