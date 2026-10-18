import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245
import BusyBeaver.ZFC.SitesRouting245Batch001
import BusyBeaver.ZFC.SitesRouting245Batch002
import BusyBeaver.ZFC.SitesRouting245Batch003
import BusyBeaver.ZFC.SitesRouting245Batch004
import BusyBeaver.ZFC.SitesRouting245Batch005
import BusyBeaver.ZFC.SitesRouting245Batch006
import BusyBeaver.ZFC.SitesRouting245Batch007
import BusyBeaver.ZFC.SitesRouting245Batch008

/-!
Closed coverage of the exact routed245 instruction tree. Every new cut is a
kernel decision about the imported actual subtree with its complete reverse
prefix; every composition requires both actual children. The three measured
pilot modules and thirteen passed original batches are reused directly. No external coverage premise, native proof
evaluation, or enlarged proof limits. Grouping changes only file boundaries.
Adapted from the maintained permutation252/prefix246 coverage generators,
preserving Mira-Cult, Jeff Ketchersid and Wade's program/simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesRouting245
open RegisterPath RMBisim SiteCoverage

theorem join_0 :
    allSites SiteRouting245.checkSite [false, false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_6 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_7

theorem join_1 :
    allSites SiteRouting245.checkSite [false, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_0 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_8

theorem join_2 :
    allSites SiteRouting245.checkSite [false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_10 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_11

theorem join_3 :
    allSites SiteRouting245.checkSite [true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_12 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_13

theorem join_4 :
    allSites SiteRouting245.checkSite [true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_2 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_3

theorem join_5 :
    allSites SiteRouting245.checkSite [false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_9 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_4

theorem join_6 :
    allSites SiteRouting245.checkSite [false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_14 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_15

theorem join_7 :
    allSites SiteRouting245.checkSite [false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_6 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_16

theorem join_8 :
    allSites SiteRouting245.checkSite [false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_17 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_18

theorem join_9 :
    allSites SiteRouting245.checkSite [false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_19 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_20

theorem join_10 :
    allSites SiteRouting245.checkSite [true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_23 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_24

theorem join_11 :
    allSites SiteRouting245.checkSite [false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_22 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_10

theorem join_12 :
    allSites SiteRouting245.checkSite [false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_26 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_27

theorem join_13 :
    allSites SiteRouting245.checkSite [true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_12 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_28

theorem join_14 :
    allSites SiteRouting245.checkSite [true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_25 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_13

theorem join_15 :
    allSites SiteRouting245.checkSite [true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_11 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_14


end SetTheory.BusyBeaver.ZFC.SitesRouting245
