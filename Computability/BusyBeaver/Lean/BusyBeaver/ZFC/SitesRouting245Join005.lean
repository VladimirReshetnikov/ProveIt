import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245
import BusyBeaver.ZFC.SitesRouting245Join004
import BusyBeaver.ZFC.SitesRouting245Cut097
import BusyBeaver.ZFC.SitesRouting245Cut098
import BusyBeaver.ZFC.SitesRouting245Cut100
import BusyBeaver.ZFC.SitesRouting245Cut101
import BusyBeaver.ZFC.SitesRouting245Cut099
import BusyBeaver.ZFC.SitesRouting245Cut102
import BusyBeaver.ZFC.SitesRouting245Join001
import BusyBeaver.ZFC.SitesRouting245Cut104
import BusyBeaver.ZFC.SitesRouting245Cut105
import BusyBeaver.ZFC.SitesRouting245Cut106
import BusyBeaver.ZFC.SitesRouting245Cut103
import BusyBeaver.ZFC.SitesRouting245Cut108
import BusyBeaver.ZFC.SitesRouting245Cut109
import BusyBeaver.ZFC.SitesRouting245Cut107
import BusyBeaver.ZFC.SitesRouting245Cut110
import BusyBeaver.ZFC.SitesRouting245Cut111

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

theorem join_80 :
    allSites SiteRouting245.checkSite [false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_79 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_97

theorem join_81 :
    allSites SiteRouting245.checkSite [false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_80 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_98

theorem join_82 :
    allSites SiteRouting245.checkSite [true, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_100 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_101

theorem join_83 :
    allSites SiteRouting245.checkSite [false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_99 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_82

theorem join_84 :
    allSites SiteRouting245.checkSite [true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_83 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_102

theorem join_85 :
    allSites SiteRouting245.checkSite [true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_81 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_84

theorem join_86 :
    allSites SiteRouting245.checkSite [true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_78 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_85

theorem join_87 :
    allSites SiteRouting245.checkSite [true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_70 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_86

theorem join_88 :
    allSites SiteRouting245.checkSite [true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_29 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_87

theorem join_89 :
    allSites SiteRouting245.checkSite [false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_23 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_88

theorem join_90 :
    allSites SiteRouting245.checkSite [false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_104 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_105

theorem join_91 :
    allSites SiteRouting245.checkSite [true, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_90 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_106

theorem join_92 :
    allSites SiteRouting245.checkSite [false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_103 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_91

theorem join_93 :
    allSites SiteRouting245.checkSite [true, false, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_108 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_109

theorem join_94 :
    allSites SiteRouting245.checkSite [false, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_107 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_93

theorem join_95 :
    allSites SiteRouting245.checkSite [false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_110 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_111


end SetTheory.BusyBeaver.ZFC.SitesRouting245
