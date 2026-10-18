import BusyBeaver.ZFC.SitesPrefix246Join001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_16
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_17
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_18
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_19
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_20
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_21
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_22
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_23
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_24
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_25
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_26
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_27
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_28
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_29
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_30
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_31

example : allSites SitePrefix246.checkSite [true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true]) = true := join_16

example : allSites SitePrefix246.checkSite [true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true]) = true := join_17

example : allSites SitePrefix246.checkSite [true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true]) = true := join_18

example : allSites SitePrefix246.checkSite [false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false]) = true := join_19

example : allSites SitePrefix246.checkSite [false, false, true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false, false]) = true := join_20

example : allSites SitePrefix246.checkSite [false, true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true, false]) = true := join_21

example : allSites SitePrefix246.checkSite [true, false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false, true]) = true := join_22

example : allSites SitePrefix246.checkSite [false, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false]) = true := join_23

example : allSites SitePrefix246.checkSite [false, false, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false, false]) = true := join_24

example : allSites SitePrefix246.checkSite [false, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, false]) = true := join_25

example : allSites SitePrefix246.checkSite [false, true, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true, false]) = true := join_26

example : allSites SitePrefix246.checkSite [true, false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false, true]) = true := join_27

example : allSites SitePrefix246.checkSite [false, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, false]) = true := join_28

example : allSites SitePrefix246.checkSite [true, false, true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false, true]) = true := join_29

example : allSites SitePrefix246.checkSite [false, true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true, false]) = true := join_30

example : allSites SitePrefix246.checkSite [true, true, true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true, true]) = true := join_31
