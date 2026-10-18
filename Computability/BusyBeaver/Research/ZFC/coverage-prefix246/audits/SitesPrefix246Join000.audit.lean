import BusyBeaver.ZFC.SitesPrefix246Join000

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesPrefix246

#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_0
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_1
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_2
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_3
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_4
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_5
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_6
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_7
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_8
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_9
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_10
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_11
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_12
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_13
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_14
#print axioms SetTheory.BusyBeaver.ZFC.SitesPrefix246.join_15

example : allSites SitePrefix246.checkSite [false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false]) = true := join_0

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, false]) = true := join_1

example : allSites SitePrefix246.checkSite [false, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, false]) = true := join_2

example : allSites SitePrefix246.checkSite [true, true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true, true]) = true := join_3

example : allSites SitePrefix246.checkSite [true, false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false, true]) = true := join_4

example : allSites SitePrefix246.checkSite [false, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false]) = true := join_5

example : allSites SitePrefix246.checkSite [false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false]) = true := join_6

example : allSites SitePrefix246.checkSite [false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false]) = true := join_7

example : allSites SitePrefix246.checkSite [false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false]) = true := join_8

example : allSites SitePrefix246.checkSite [true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true]) = true := join_9

example : allSites SitePrefix246.checkSite [true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true]) = true := join_10

example : allSites SitePrefix246.checkSite [true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true]) = true := join_11

example : allSites SitePrefix246.checkSite [false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false]) = true := join_12

example : allSites SitePrefix246.checkSite [true, false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false, true]) = true := join_13

example : allSites SitePrefix246.checkSite [false, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, false]) = true := join_14

example : allSites SitePrefix246.checkSite [false, true, true, true, false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true, true, true, false]) = true := join_15
