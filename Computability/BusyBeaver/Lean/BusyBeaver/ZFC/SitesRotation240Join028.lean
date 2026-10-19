import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Batch460
import BusyBeaver.ZFC.SitesRotation240Batch461
import BusyBeaver.ZFC.SitesRotation240Batch459
import BusyBeaver.ZFC.SitesRotation240Batch458
import BusyBeaver.ZFC.SitesRotation240Batch462
import BusyBeaver.ZFC.SitesRotation240Batch463
import BusyBeaver.ZFC.SitesRotation240Batch464
import BusyBeaver.ZFC.SitesRotation240Batch465
import BusyBeaver.ZFC.SitesRotation240Batch466
import BusyBeaver.ZFC.SitesRotation240Batch467
import BusyBeaver.ZFC.SitesRotation240Batch468
import BusyBeaver.ZFC.SitesRotation240Batch469
import BusyBeaver.ZFC.SitesRotation240Batch472
import BusyBeaver.ZFC.SitesRotation240Batch473
import BusyBeaver.ZFC.SitesRotation240Batch471
import BusyBeaver.ZFC.SitesRotation240Batch470
import BusyBeaver.ZFC.SitesRotation240Batch474
import BusyBeaver.ZFC.SitesRotation240Batch475
import BusyBeaver.ZFC.SitesRotation240Batch476

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

theorem join_448 :
    allSites SiteRotation240.checkSite [true, true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_462 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_463

theorem join_449 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_461 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_448

theorem join_450 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_460 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_449

theorem join_451 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_464 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_465

theorem join_452 :
    allSites SiteRotation240.checkSite [true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_451 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_466

theorem join_453 :
    allSites SiteRotation240.checkSite [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_450 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_452

theorem join_454 :
    allSites SiteRotation240.checkSite [false, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_467 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_468

theorem join_455 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_454 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_469

theorem join_456 :
    allSites SiteRotation240.checkSite [true, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_470 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_471

theorem join_457 :
    allSites SiteRotation240.checkSite [false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_455 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_456

theorem join_458 :
    allSites SiteRotation240.checkSite [true, true, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_474 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_475

theorem join_459 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_473 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_458

theorem join_460 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_472 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_459

theorem join_461 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_476 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_477

theorem join_462 :
    allSites SiteRotation240.checkSite [true, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_461 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_478

theorem join_463 :
    allSites SiteRotation240.checkSite [false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_460 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_462


end SetTheory.BusyBeaver.ZFC.SitesRotation240
