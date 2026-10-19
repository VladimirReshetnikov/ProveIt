import BusyBeaver.ZFC.SitesRotation240Join004

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_64
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_65
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_66
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_67
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_68
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_69
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_70
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_71
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_72
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_73
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_74
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_75
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_76
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_77
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_78
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_79

example : allSites SiteRotation240.checkSite [false, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false]) = true := join_64

example : allSites SiteRotation240.checkSite [false, false, true, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, true, false, false]) = true := join_65

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, true, false]) = true := join_66

example : allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, true, true, true]) = true := join_67

example : allSites SiteRotation240.checkSite [true, true, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, true, true]) = true := join_68

example : allSites SiteRotation240.checkSite [true, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, true]) = true := join_69

example : allSites SiteRotation240.checkSite [false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false]) = true := join_70

example : allSites SiteRotation240.checkSite [true, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, true]) = true := join_71

example : allSites SiteRotation240.checkSite [true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true]) = true := join_72

example : allSites SiteRotation240.checkSite [false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false]) = true := join_73

example : allSites SiteRotation240.checkSite [false, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, false]) = true := join_74

example : allSites SiteRotation240.checkSite [false, false, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, false, false]) = true := join_75

example : allSites SiteRotation240.checkSite [false, true, false, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, false, true, false]) = true := join_76

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, false, true, true, false]) = true := join_77

example : allSites SiteRotation240.checkSite [true, true, false, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, false, true, true]) = true := join_78

example : allSites SiteRotation240.checkSite [true, false, true, false, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, false, true, false, true]) = true := join_79
