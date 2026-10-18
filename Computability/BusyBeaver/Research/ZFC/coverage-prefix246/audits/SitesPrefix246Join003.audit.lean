import BusyBeaver.ZFC.SitesPrefix246Join003

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_48
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_49
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_50
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_51
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_52
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_53
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_54
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_55
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_56
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_57
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_58
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_59
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_60
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_61
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_62
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_63

example : allSites SitePrefix246.checkSite [true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true]) = true := join_48

example : allSites SitePrefix246.checkSite [true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true]) = true := join_49

example : allSites SitePrefix246.checkSite [false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false]) = true := join_50

example : allSites SitePrefix246.checkSite [false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false]) = true := join_51

example : allSites SitePrefix246.checkSite [false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false]) = true := join_52

example : allSites SitePrefix246.checkSite [true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true]) = true := join_53

example : allSites SitePrefix246.checkSite [false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false]) = true := join_54

example : allSites SitePrefix246.checkSite [false, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, false]) = true := join_55

example : allSites SitePrefix246.checkSite [false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false]) = true := join_56

example : allSites SitePrefix246.checkSite [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false]) = true := join_57

example : allSites SitePrefix246.checkSite [true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true]) = true := join_58

example : allSites SitePrefix246.checkSite [true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true]) = true := join_59

example : allSites SitePrefix246.checkSite [true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true]) = true := join_60

example : allSites SitePrefix246.checkSite [false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false]) = true := join_61

example : allSites SitePrefix246.checkSite [true, false, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false, true]) = true := join_62

example : allSites SitePrefix246.checkSite [false, false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false]) = true := join_63
