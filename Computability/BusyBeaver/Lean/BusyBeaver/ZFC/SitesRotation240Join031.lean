import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Join030
import BusyBeaver.ZFC.SitesRotation240Batch509
import BusyBeaver.ZFC.SitesRotation240Join029
import BusyBeaver.ZFC.SitesRotation240Join001
import BusyBeaver.ZFC.SitesRotation240Join000
import BusyBeaver.ZFC.SitesRotation240PilotChanged
import BusyBeaver.ZFC.SitesRotation240Batch510
import BusyBeaver.ZFC.SitesRotation240Batch511
import BusyBeaver.ZFC.SitesRotation240Batch005
import BusyBeaver.ZFC.SitesRotation240PilotHalt
import BusyBeaver.ZFC.SitesRotation240Batch513
import BusyBeaver.ZFC.SitesRotation240Batch512

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

theorem join_496 :
    allSites SiteRotation240.checkSite [false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_491 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_495

theorem join_497 :
    allSites SiteRotation240.checkSite [true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_496 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_511

theorem join_498 :
    allSites SiteRotation240.checkSite [true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_489 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_497

theorem join_499 :
    allSites SiteRotation240.checkSite [true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_482 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_498

theorem join_500 :
    allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_478 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_499

theorem join_501 :
    allSites SiteRotation240.checkSite [true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_469 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_500

theorem join_502 :
    allSites SiteRotation240.checkSite [true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_20 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_501

theorem join_503 :
    allSites SiteRotation240.checkSite [false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_15 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_502

theorem join_504 :
    allSites SiteRotation240.checkSite [true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240PilotChanged.checked SetTheory.BusyBeaver.ZFC.SitesRotation240.block_513

theorem join_505 :
    allSites SiteRotation240.checkSite [true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_503 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_504

theorem join_506 :
    allSites SiteRotation240.checkSite [false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_5 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_505

theorem join_507 :
    allSites SiteRotation240.checkSite [true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_506 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_514

theorem join_508 :
    allSites SiteRotation240.checkSite [false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_5 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_507

theorem join_509 :
    allSites SiteRotation240.checkSite [true, true, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240PilotHalt.checked SetTheory.BusyBeaver.ZFC.SitesRotation240.block_517

theorem join_510 :
    allSites SiteRotation240.checkSite [true, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_515 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_509

theorem join_511 :
    allSites SiteRotation240.checkSite [false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_508 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_510


end SetTheory.BusyBeaver.ZFC.SitesRotation240
