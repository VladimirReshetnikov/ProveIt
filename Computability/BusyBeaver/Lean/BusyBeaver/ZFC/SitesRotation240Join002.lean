import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Join001
import BusyBeaver.ZFC.SitesRotation240Batch047
import BusyBeaver.ZFC.SitesRotation240Batch048
import BusyBeaver.ZFC.SitesRotation240Batch049
import BusyBeaver.ZFC.SitesRotation240Batch050
import BusyBeaver.ZFC.SitesRotation240Batch051
import BusyBeaver.ZFC.SitesRotation240Batch052
import BusyBeaver.ZFC.SitesRotation240Batch053
import BusyBeaver.ZFC.SitesRotation240Batch046
import BusyBeaver.ZFC.SitesRotation240Batch057
import BusyBeaver.ZFC.SitesRotation240Batch058
import BusyBeaver.ZFC.SitesRotation240Batch056
import BusyBeaver.ZFC.SitesRotation240Batch055
import BusyBeaver.ZFC.SitesRotation240Batch059
import BusyBeaver.ZFC.SitesRotation240Batch060
import BusyBeaver.ZFC.SitesRotation240Batch061

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

theorem join_32 :
    allSites SiteRotation240.checkSite [true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_29 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_31

theorem join_33 :
    allSites SiteRotation240.checkSite [false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_28 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_32

theorem join_34 :
    allSites SiteRotation240.checkSite [false, false, false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_48 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_49

theorem join_35 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_34 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_50

theorem join_36 :
    allSites SiteRotation240.checkSite [false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_35 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_51

theorem join_37 :
    allSites SiteRotation240.checkSite [false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_52 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_53

theorem join_38 :
    allSites SiteRotation240.checkSite [true, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_37 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_54

theorem join_39 :
    allSites SiteRotation240.checkSite [true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_36 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_38

theorem join_40 :
    allSites SiteRotation240.checkSite [true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_47 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_39

theorem join_41 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_33 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_40

theorem join_42 :
    allSites SiteRotation240.checkSite [false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_27 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_41

theorem join_43 :
    allSites SiteRotation240.checkSite [true, true, false, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_58 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_59

theorem join_44 :
    allSites SiteRotation240.checkSite [true, false, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_57 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_43

theorem join_45 :
    allSites SiteRotation240.checkSite [false, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_56 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_44

theorem join_46 :
    allSites SiteRotation240.checkSite [false, true, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_60 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_61

theorem join_47 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_46 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_62


end SetTheory.BusyBeaver.ZFC.SitesRotation240
