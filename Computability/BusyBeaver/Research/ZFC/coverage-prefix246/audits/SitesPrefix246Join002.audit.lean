import BusyBeaver.ZFC.SitesPrefix246Join002

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_32
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_33
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_34
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_35
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_36
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_37
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_38
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_39
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_40
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_41
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_42
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_43
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_44
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_45
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_46
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_47

example : allSites SitePrefix246.checkSite [true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true]) = true := join_32

example : allSites SitePrefix246.checkSite [true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true]) = true := join_33

example : allSites SitePrefix246.checkSite [false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false]) = true := join_34

example : allSites SitePrefix246.checkSite [true, false, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, false, true]) = true := join_35

example : allSites SitePrefix246.checkSite [false, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, false]) = true := join_36

example : allSites SitePrefix246.checkSite [false, true, true, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, true, true, false]) = true := join_37

example : allSites SitePrefix246.checkSite [true, true, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, true, true]) = true := join_38

example : allSites SitePrefix246.checkSite [true, true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true, true]) = true := join_39

example : allSites SitePrefix246.checkSite [true, false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false, true]) = true := join_40

example : allSites SitePrefix246.checkSite [false, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false]) = true := join_41

example : allSites SitePrefix246.checkSite [false, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, false, false]) = true := join_42

example : allSites SitePrefix246.checkSite [false, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, false]) = true := join_43

example : allSites SitePrefix246.checkSite [false, false, true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true, false, false]) = true := join_44

example : allSites SitePrefix246.checkSite [false, true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true, false]) = true := join_45

example : allSites SitePrefix246.checkSite [true, true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true, true]) = true := join_46

example : allSites SitePrefix246.checkSite [true, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, true]) = true := join_47
