import BusyBeaver.ZFC.SitesRotation240Join003

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open RegisterPath RMBisim SiteCoverage SitesRotation240

#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_48
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_49
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_50
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_51
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_52
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_53
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_54
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_55
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_56
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_57
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_58
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_59
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_60
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_61
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_62
#print axioms SetTheory.BusyBeaver.ZFC.SitesRotation240.join_63

example : allSites SiteRotation240.checkSite [false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false]) = true := join_48

example : allSites SiteRotation240.checkSite [false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false]) = true := join_49

example : allSites SiteRotation240.checkSite [false, false, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false, false]) = true := join_50

example : allSites SiteRotation240.checkSite [true, false, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false, true]) = true := join_51

example : allSites SiteRotation240.checkSite [false, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false]) = true := join_52

example : allSites SiteRotation240.checkSite [true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, true]) = true := join_53

example : allSites SiteRotation240.checkSite [true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true]) = true := join_54

example : allSites SiteRotation240.checkSite [true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true]) = true := join_55

example : allSites SiteRotation240.checkSite [false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false]) = true := join_56

example : allSites SiteRotation240.checkSite [true, true, false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true]) = true := join_57

example : allSites SiteRotation240.checkSite [true, false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, true]) = true := join_58

example : allSites SiteRotation240.checkSite [false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false]) = true := join_59

example : allSites SiteRotation240.checkSite [false, true, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true, false]) = true := join_60

example : allSites SiteRotation240.checkSite [true, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true]) = true := join_61

example : allSites SiteRotation240.checkSite [false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false]) = true := join_62

example : allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false, true]) = true := join_63
