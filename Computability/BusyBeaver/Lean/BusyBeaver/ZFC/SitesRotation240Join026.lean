import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Join025
import BusyBeaver.ZFC.SitesRotation240Join024
import BusyBeaver.ZFC.SitesRotation240Batch433
import BusyBeaver.ZFC.SitesRotation240Batch434
import BusyBeaver.ZFC.SitesRotation240Batch432
import BusyBeaver.ZFC.SitesRotation240Batch435
import BusyBeaver.ZFC.SitesRotation240Batch436
import BusyBeaver.ZFC.SitesRotation240Batch437
import BusyBeaver.ZFC.SitesRotation240Batch439
import BusyBeaver.ZFC.SitesRotation240Batch440
import BusyBeaver.ZFC.SitesRotation240Batch438
import BusyBeaver.ZFC.SitesRotation240Batch442
import BusyBeaver.ZFC.SitesRotation240Batch443
import BusyBeaver.ZFC.SitesRotation240Batch441
import BusyBeaver.ZFC.SitesRotation240Batch444
import BusyBeaver.ZFC.SitesRotation240Batch445

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

theorem join_416 :
    allSites SiteRotation240.checkSite [true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_413 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_415

theorem join_417 :
    allSites SiteRotation240.checkSite [true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_412 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_416

theorem join_418 :
    allSites SiteRotation240.checkSite [true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_410 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_417

theorem join_419 :
    allSites SiteRotation240.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_406 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_418

theorem join_420 :
    allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_385 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_419

theorem join_421 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_435 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_436

theorem join_422 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_434 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_421

theorem join_423 :
    allSites SiteRotation240.checkSite [false, false, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_437 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_438

theorem join_424 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_423 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_439

theorem join_425 :
    allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_441 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_442

theorem join_426 :
    allSites SiteRotation240.checkSite [true, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_440 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_425

theorem join_427 :
    allSites SiteRotation240.checkSite [true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_424 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_426

theorem join_428 :
    allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_422 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_427

theorem join_429 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_444 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_445

theorem join_430 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_443 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_429

theorem join_431 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, true, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_446 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_447


end SetTheory.BusyBeaver.ZFC.SitesRotation240
