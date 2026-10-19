import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Join002
import BusyBeaver.ZFC.SitesRotation240Batch062
import BusyBeaver.ZFC.SitesRotation240Batch063
import BusyBeaver.ZFC.SitesRotation240Batch064
import BusyBeaver.ZFC.SitesRotation240Batch065
import BusyBeaver.ZFC.SitesRotation240Batch066
import BusyBeaver.ZFC.SitesRotation240Batch067
import BusyBeaver.ZFC.SitesRotation240Batch068
import BusyBeaver.ZFC.SitesRotation240Batch054
import BusyBeaver.ZFC.SitesRotation240Batch071
import BusyBeaver.ZFC.SitesRotation240Batch072
import BusyBeaver.ZFC.SitesRotation240Batch070
import BusyBeaver.ZFC.SitesRotation240Batch069
import BusyBeaver.ZFC.SitesRotation240Batch073
import BusyBeaver.ZFC.SitesRotation240Batch074
import BusyBeaver.ZFC.SitesRotation240Batch075
import BusyBeaver.ZFC.SitesRotation240Batch077
import BusyBeaver.ZFC.SitesRotation240Batch078

/-!
Closed coverage of the exact direct240 instruction tree. Every new cut is a
kernel decision about the imported actual subtree with its complete reverse
prefix; every composition requires both actual children. The four measured
pilot modules are reused directly. No external coverage premise, native proof
evaluation, or enlarged proof limits. Grouping changes only file boundaries.
Adapted from the maintained permutation252/prefix246 coverage generators,
preserving Mira-Cult, Jeff Ketchersid and Wade's program/simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesRotation240
open RegisterPath RMBisim SiteCoverage

theorem join_48 :
    allSites SiteRotation240.checkSite [false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_45 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_47

theorem join_49 :
    allSites SiteRotation240.checkSite [false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_48 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_63

theorem join_50 :
    allSites SiteRotation240.checkSite [false, false, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_64 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_65

theorem join_51 :
    allSites SiteRotation240.checkSite [true, false, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_66 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_67

theorem join_52 :
    allSites SiteRotation240.checkSite [false, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_50 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_51

theorem join_53 :
    allSites SiteRotation240.checkSite [true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_68 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_69

theorem join_54 :
    allSites SiteRotation240.checkSite [true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_52 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_53

theorem join_55 :
    allSites SiteRotation240.checkSite [true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_49 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_54

theorem join_56 :
    allSites SiteRotation240.checkSite [false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_55 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_55

theorem join_57 :
    allSites SiteRotation240.checkSite [true, true, false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_72 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_73

theorem join_58 :
    allSites SiteRotation240.checkSite [true, false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_71 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_57

theorem join_59 :
    allSites SiteRotation240.checkSite [false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_70 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_58

theorem join_60 :
    allSites SiteRotation240.checkSite [false, true, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_74 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_75

theorem join_61 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_60 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_76

theorem join_62 :
    allSites SiteRotation240.checkSite [false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_59 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_61

theorem join_63 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_78 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_79


end SetTheory.BusyBeaver.ZFC.SitesRotation240
