import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Batch007
import BusyBeaver.ZFC.SitesRotation240Batch008
import BusyBeaver.ZFC.SitesRotation240Batch006
import BusyBeaver.ZFC.SitesRotation240PilotLongZero
import BusyBeaver.ZFC.SitesRotation240Batch009
import BusyBeaver.ZFC.SitesRotation240Batch010
import BusyBeaver.ZFC.SitesRotation240Batch011
import BusyBeaver.ZFC.SitesRotation240Batch013
import BusyBeaver.ZFC.SitesRotation240Batch014
import BusyBeaver.ZFC.SitesRotation240Batch015
import BusyBeaver.ZFC.SitesRotation240Batch017
import BusyBeaver.ZFC.SitesRotation240Batch018
import BusyBeaver.ZFC.SitesRotation240Batch016
import BusyBeaver.ZFC.SitesRotation240Batch019
import BusyBeaver.ZFC.SitesRotation240Batch020
import BusyBeaver.ZFC.SitesRotation240Batch021
import BusyBeaver.ZFC.SitesRotation240Batch022
import BusyBeaver.ZFC.SitesRotation240Batch012

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

theorem join_0 :
    allSites SiteRotation240.checkSite [true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_8 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_9

theorem join_1 :
    allSites SiteRotation240.checkSite [true, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_7 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_0

theorem join_2 :
    allSites SiteRotation240.checkSite [false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240PilotLongZero.checked SetTheory.BusyBeaver.ZFC.SitesRotation240.join_1

theorem join_3 :
    allSites SiteRotation240.checkSite [false, true, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_10 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_11

theorem join_4 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_3 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_12

theorem join_5 :
    allSites SiteRotation240.checkSite [false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_2 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_4

theorem join_6 :
    allSites SiteRotation240.checkSite [false, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_14 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_15

theorem join_7 :
    allSites SiteRotation240.checkSite [false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_6 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_16

theorem join_8 :
    allSites SiteRotation240.checkSite [true, true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_18 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_19

theorem join_9 :
    allSites SiteRotation240.checkSite [true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_17 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_8

theorem join_10 :
    allSites SiteRotation240.checkSite [false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_7 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_9

theorem join_11 :
    allSites SiteRotation240.checkSite [false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_20 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_21

theorem join_12 :
    allSites SiteRotation240.checkSite [true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_22 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_23

theorem join_13 :
    allSites SiteRotation240.checkSite [true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_11 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_12

theorem join_14 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_10 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_13

theorem join_15 :
    allSites SiteRotation240.checkSite [false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_13 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_14


end SetTheory.BusyBeaver.ZFC.SitesRotation240
