import BusyBeaver.ZFC.SitesPrefix246Join004

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_64
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_65
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_66
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_67
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_68
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_69
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_70
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_71
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_72
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_73
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_74
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_75
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_76
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_77
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_78
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_79

example : allSites SitePrefix246.checkSite [false, true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, true, false]) = true := join_64

example : allSites SitePrefix246.checkSite [true, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, true]) = true := join_65

example : allSites SitePrefix246.checkSite [false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false]) = true := join_66

example : allSites SitePrefix246.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false]) = true := join_67

example : allSites SitePrefix246.checkSite [false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false]) = true := join_68

example : allSites SitePrefix246.checkSite [true, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, true]) = true := join_69

example : allSites SitePrefix246.checkSite [true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true]) = true := join_70

example : allSites SitePrefix246.checkSite [false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false]) = true := join_71

example : allSites SitePrefix246.checkSite [false, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false]) = true := join_72

example : allSites SitePrefix246.checkSite [false, true, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, true, false]) = true := join_73

example : allSites SitePrefix246.checkSite [true, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, true]) = true := join_74

example : allSites SitePrefix246.checkSite [false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false]) = true := join_75

example : allSites SitePrefix246.checkSite [false, false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false, false]) = true := join_76

example : allSites SitePrefix246.checkSite [false, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false]) = true := join_77

example : allSites SitePrefix246.checkSite [false, true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, true, false]) = true := join_78

example : allSites SitePrefix246.checkSite [true, true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, true]) = true := join_79
