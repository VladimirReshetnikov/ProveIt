import BusyBeaver.ZFC.SitesRouting245Join000

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRouting245

#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_0
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_1
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_2
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_3
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_4
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_5
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_6
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_7
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_8
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_9
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_10
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_11
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_12
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_13
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_14
#print axioms SetTheory.BusyBeaver.ZFC.SitesRouting245.join_15

example : allSites SiteRouting245.checkSite [false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false]) = true := join_0

example : allSites SiteRouting245.checkSite [false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false]) = true := join_1

example : allSites SiteRouting245.checkSite [false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false]) = true := join_2

example : allSites SiteRouting245.checkSite [true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true]) = true := join_3

example : allSites SiteRouting245.checkSite [true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true]) = true := join_4

example : allSites SiteRouting245.checkSite [false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false]) = true := join_5

example : allSites SiteRouting245.checkSite [false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false]) = true := join_6

example : allSites SiteRouting245.checkSite [false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false]) = true := join_7

example : allSites SiteRouting245.checkSite [false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false]) = true := join_8

example : allSites SiteRouting245.checkSite [false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false]) = true := join_9

example : allSites SiteRouting245.checkSite [true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true]) = true := join_10

example : allSites SiteRouting245.checkSite [false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false]) = true := join_11

example : allSites SiteRouting245.checkSite [false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false]) = true := join_12

example : allSites SiteRouting245.checkSite [true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true]) = true := join_13

example : allSites SiteRouting245.checkSite [true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true]) = true := join_14

example : allSites SiteRouting245.checkSite [true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true]) = true := join_15
