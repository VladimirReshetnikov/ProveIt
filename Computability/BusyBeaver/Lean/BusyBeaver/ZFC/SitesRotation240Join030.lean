import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Join029
import BusyBeaver.ZFC.SitesRotation240Batch490
import BusyBeaver.ZFC.SitesRotation240Batch491
import BusyBeaver.ZFC.SitesRotation240Batch492
import BusyBeaver.ZFC.SitesRotation240Batch494
import BusyBeaver.ZFC.SitesRotation240Batch495
import BusyBeaver.ZFC.SitesRotation240Batch493
import BusyBeaver.ZFC.SitesRotation240Batch496
import BusyBeaver.ZFC.SitesRotation240Batch497
import BusyBeaver.ZFC.SitesRotation240Batch499
import BusyBeaver.ZFC.SitesRotation240Batch500
import BusyBeaver.ZFC.SitesRotation240Batch498
import BusyBeaver.ZFC.SitesRotation240Batch502
import BusyBeaver.ZFC.SitesRotation240Batch503
import BusyBeaver.ZFC.SitesRotation240Batch501
import BusyBeaver.ZFC.SitesRotation240Batch504
import BusyBeaver.ZFC.SitesRotation240Batch505
import BusyBeaver.ZFC.SitesRotation240Batch507
import BusyBeaver.ZFC.SitesRotation240Batch508
import BusyBeaver.ZFC.SitesRotation240Batch506

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

theorem join_480 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_479 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_492

theorem join_481 :
    allSites SiteRotation240.checkSite [true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_493 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_494

theorem join_482 :
    allSites SiteRotation240.checkSite [false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_480 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_481

theorem join_483 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_496 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_497

theorem join_484 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_495 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_483

theorem join_485 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_498 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_499

theorem join_486 :
    allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_501 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_502

theorem join_487 :
    allSites SiteRotation240.checkSite [true, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_500 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_486

theorem join_488 :
    allSites SiteRotation240.checkSite [true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_485 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_487

theorem join_489 :
    allSites SiteRotation240.checkSite [false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_484 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_488

theorem join_490 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_504 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_505

theorem join_491 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_503 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_490

theorem join_492 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_506 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_507

theorem join_493 :
    allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_509 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_510

theorem join_494 :
    allSites SiteRotation240.checkSite [true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_508 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_493

theorem join_495 :
    allSites SiteRotation240.checkSite [true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_492 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_494


end SetTheory.BusyBeaver.ZFC.SitesRotation240
