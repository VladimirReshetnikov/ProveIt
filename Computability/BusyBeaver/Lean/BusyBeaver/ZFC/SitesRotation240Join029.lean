import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Join028
import BusyBeaver.ZFC.SitesRotation240Batch477
import BusyBeaver.ZFC.SitesRotation240Join027
import BusyBeaver.ZFC.SitesRotation240Join001
import BusyBeaver.ZFC.SitesRotation240Batch478
import BusyBeaver.ZFC.SitesRotation240Batch479
import BusyBeaver.ZFC.SitesRotation240Batch482
import BusyBeaver.ZFC.SitesRotation240Batch483
import BusyBeaver.ZFC.SitesRotation240Batch481
import BusyBeaver.ZFC.SitesRotation240Batch480
import BusyBeaver.ZFC.SitesRotation240Batch484
import BusyBeaver.ZFC.SitesRotation240Batch485
import BusyBeaver.ZFC.SitesRotation240Batch486
import BusyBeaver.ZFC.SitesRotation240Batch487
import BusyBeaver.ZFC.SitesRotation240Batch488
import BusyBeaver.ZFC.SitesRotation240Batch489

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

theorem join_464 :
    allSites SiteRotation240.checkSite [true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_463 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_479

theorem join_465 :
    allSites SiteRotation240.checkSite [true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_457 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_464

theorem join_466 :
    allSites SiteRotation240.checkSite [true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_453 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_465

theorem join_467 :
    allSites SiteRotation240.checkSite [true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_447 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_466

theorem join_468 :
    allSites SiteRotation240.checkSite [true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_446 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_467

theorem join_469 :
    allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_23 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_468

theorem join_470 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_480 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_481

theorem join_471 :
    allSites SiteRotation240.checkSite [true, true, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_484 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_485

theorem join_472 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_483 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_471

theorem join_473 :
    allSites SiteRotation240.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_482 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_472

theorem join_474 :
    allSites SiteRotation240.checkSite [false, true, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_486 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_487

theorem join_475 :
    allSites SiteRotation240.checkSite [true, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_474 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_488

theorem join_476 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_473 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_475

theorem join_477 :
    allSites SiteRotation240.checkSite [true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_476 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_489

theorem join_478 :
    allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_470 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_477

theorem join_479 :
    allSites SiteRotation240.checkSite [false, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_490 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_491


end SetTheory.BusyBeaver.ZFC.SitesRotation240
