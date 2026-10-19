import BusyBeaver.ZFC.SitesRotation240Join001

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_16
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_17
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_18
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_19
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_20
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_21
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_22
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_23
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_24
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_25
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_26
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_27
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_28
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_29
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_30
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_31

example : allSites SiteRotation240.checkSite [false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false]) = true := join_16

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true]) = true := join_17

example : allSites SiteRotation240.checkSite [false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false]) = true := join_18

example : allSites SiteRotation240.checkSite [true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true]) = true := join_19

example : allSites SiteRotation240.checkSite [false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false]) = true := join_20

example : allSites SiteRotation240.checkSite [false, false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false]) = true := join_21

example : allSites SiteRotation240.checkSite [true, false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true]) = true := join_22

example : allSites SiteRotation240.checkSite [false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false]) = true := join_23

example : allSites SiteRotation240.checkSite [false, false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false]) = true := join_24

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true]) = true := join_25

example : allSites SiteRotation240.checkSite [false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false]) = true := join_26

example : allSites SiteRotation240.checkSite [false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false]) = true := join_27

example : allSites SiteRotation240.checkSite [false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false]) = true := join_28

example : allSites SiteRotation240.checkSite [false, true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false]) = true := join_29

example : allSites SiteRotation240.checkSite [false, true, true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false]) = true := join_30

example : allSites SiteRotation240.checkSite [true, true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true]) = true := join_31
