import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Batch023
import BusyBeaver.ZFC.SitesRotation240Batch024
import BusyBeaver.ZFC.SitesRotation240Batch025
import BusyBeaver.ZFC.SitesRotation240Batch026
import BusyBeaver.ZFC.SitesRotation240Batch027
import BusyBeaver.ZFC.SitesRotation240Batch028
import BusyBeaver.ZFC.SitesRotation240Batch029
import BusyBeaver.ZFC.SitesRotation240Batch030
import BusyBeaver.ZFC.SitesRotation240Batch031
import BusyBeaver.ZFC.SitesRotation240Batch032
import BusyBeaver.ZFC.SitesRotation240Batch033
import BusyBeaver.ZFC.SitesRotation240Batch034
import BusyBeaver.ZFC.SitesRotation240Batch035
import BusyBeaver.ZFC.SitesRotation240Batch036
import BusyBeaver.ZFC.SitesRotation240Batch037
import BusyBeaver.ZFC.SitesRotation240Batch038
import BusyBeaver.ZFC.SitesRotation240Batch039
import BusyBeaver.ZFC.SitesRotation240Batch040
import BusyBeaver.ZFC.SitesRotation240Batch041
import BusyBeaver.ZFC.SitesRotation240Batch042
import BusyBeaver.ZFC.SitesRotation240Batch043
import BusyBeaver.ZFC.SitesRotation240Batch044
import BusyBeaver.ZFC.SitesRotation240Batch045

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

theorem join_16 :
    allSites SiteRotation240.checkSite [false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_24 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_25

theorem join_17 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_26 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_27

theorem join_18 :
    allSites SiteRotation240.checkSite [false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_16 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_17

theorem join_19 :
    allSites SiteRotation240.checkSite [true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_28 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_29

theorem join_20 :
    allSites SiteRotation240.checkSite [false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_18 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_19

theorem join_21 :
    allSites SiteRotation240.checkSite [false, false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_30 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_31

theorem join_22 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_32 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_33

theorem join_23 :
    allSites SiteRotation240.checkSite [false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_21 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_22

theorem join_24 :
    allSites SiteRotation240.checkSite [false, false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_34 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_35

theorem join_25 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_36 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_37

theorem join_26 :
    allSites SiteRotation240.checkSite [false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_24 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_25

theorem join_27 :
    allSites SiteRotation240.checkSite [false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_38 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_39

theorem join_28 :
    allSites SiteRotation240.checkSite [false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_40 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_41

theorem join_29 :
    allSites SiteRotation240.checkSite [false, true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_42 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_43

theorem join_30 :
    allSites SiteRotation240.checkSite [false, true, true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_44 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_45

theorem join_31 :
    allSites SiteRotation240.checkSite [true, true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_30 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_46


end SetTheory.BusyBeaver.ZFC.SitesRotation240
