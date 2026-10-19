import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Join031
import BusyBeaver.ZFC.SitesRotation240Batch514
import BusyBeaver.ZFC.SitesRotation240Batch004
import BusyBeaver.ZFC.SitesRotation240Batch515
import BusyBeaver.ZFC.SitesRotation240Batch516
import BusyBeaver.ZFC.SitesRotation240Batch517
import BusyBeaver.ZFC.SitesRotation240Batch003
import BusyBeaver.ZFC.SitesRotation240Batch518
import BusyBeaver.ZFC.SitesRotation240Batch519
import BusyBeaver.ZFC.SitesRotation240Batch520
import BusyBeaver.ZFC.SitesRotation240Batch521
import BusyBeaver.ZFC.SitesRotation240Batch522
import BusyBeaver.ZFC.SitesRotation240Batch524
import BusyBeaver.ZFC.SitesRotation240Batch525
import BusyBeaver.ZFC.SitesRotation240Batch523
import BusyBeaver.ZFC.SitesRotation240Batch002
import BusyBeaver.ZFC.SitesRotation240Batch001

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

theorem join_512 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_511 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_518

theorem join_513 :
    allSites SiteRotation240.checkSite [false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_4 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_512

theorem join_514 :
    allSites SiteRotation240.checkSite [true, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_519 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_520

theorem join_515 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_513 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_514

theorem join_516 :
    allSites SiteRotation240.checkSite [true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_515 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_521

theorem join_517 :
    allSites SiteRotation240.checkSite [false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_3 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_516

theorem join_518 :
    allSites SiteRotation240.checkSite [false, false, false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, true, true, true]
    (descend TreeRotation240.tree [true, true, true, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_522 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_523

theorem join_519 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, true, true]
    (descend TreeRotation240.tree [true, true, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_524 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_525

theorem join_520 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, true]
    (descend TreeRotation240.tree [true, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_518 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_519

theorem join_521 :
    allSites SiteRotation240.checkSite [false, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, true]
    (descend TreeRotation240.tree [true, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_520 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_526

theorem join_522 :
    allSites SiteRotation240.checkSite [true, true, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, true, true]
    (descend TreeRotation240.tree [true, true, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_528 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_529

theorem join_523 :
    allSites SiteRotation240.checkSite [true, true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, true]
    (descend TreeRotation240.tree [true, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_527 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_522

theorem join_524 :
    allSites SiteRotation240.checkSite [true, true, true, true]
      (descend TreeRotation240.tree [true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true]
    (descend TreeRotation240.tree [true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_521 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_523

theorem join_525 :
    allSites SiteRotation240.checkSite [true, true, true]
      (descend TreeRotation240.tree [true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true]
    (descend TreeRotation240.tree [true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_517 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_524

theorem join_526 :
    allSites SiteRotation240.checkSite [true, true]
      (descend TreeRotation240.tree [true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true]
    (descend TreeRotation240.tree [true, true, false])
    (descend TreeRotation240.tree [true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_2 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_525

theorem join_527 :
    allSites SiteRotation240.checkSite [true]
      (descend TreeRotation240.tree [true]) = true :=
  allSites_join SiteRotation240.checkSite [true]
    (descend TreeRotation240.tree [true, false])
    (descend TreeRotation240.tree [true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_1 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_526


end SetTheory.BusyBeaver.ZFC.SitesRotation240
