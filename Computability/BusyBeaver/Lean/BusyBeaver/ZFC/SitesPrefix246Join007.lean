import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePrefix246
import BusyBeaver.ZFC.SitesPrefix246Batch042
import BusyBeaver.ZFC.SitesPrefix246Batch043
import BusyBeaver.ZFC.SitesPrefix246Batch044
import BusyBeaver.ZFC.SitesPrefix246Batch045
import BusyBeaver.ZFC.SitesPrefix246Batch046
import BusyBeaver.ZFC.SitesPrefix246Join006
import BusyBeaver.ZFC.SitesPrefix246Batch047
import BusyBeaver.ZFC.SitesPrefix246Batch048

/-!
Generated closed actual-tree coverage for the exact246 table and checker.
Every cut is a kernel decision about the imported actual decoder subtree.
Every structural join requires both actual children. No external coverage
premise, native evaluation or enlarged proof limits. Grouping changes only
file boundaries, never the cut propositions or the full coverage statement.
Adapted from the maintained permutation252 and prefix250 generators, preserving
Mira-Cult, Jeff Ketchersid and Wade's program and simulation attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.SitesPrefix246
open RegisterPath RMBisim SiteCoverage

theorem join_112 :
    allSites SitePrefix246.checkSite [false, false, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false, false, true])
    block_122 block_123

theorem join_113 :
    allSites SitePrefix246.checkSite [false, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false, true])
    join_112 block_124

theorem join_114 :
    allSites SitePrefix246.checkSite [true, false, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, true, true])
    block_126 block_127

theorem join_115 :
    allSites SitePrefix246.checkSite [false, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false, true])
    block_125 join_114

theorem join_116 :
    allSites SitePrefix246.checkSite [true, true, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true, true])
    block_129 block_130

theorem join_117 :
    allSites SitePrefix246.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true, true])
    block_128 join_116

theorem join_118 :
    allSites SitePrefix246.checkSite [false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false, true])
    join_115 join_117

theorem join_119 :
    allSites SitePrefix246.checkSite [true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true, true])
    join_118 block_131

theorem join_120 :
    allSites SitePrefix246.checkSite [true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true, true])
    join_113 join_119

theorem join_121 :
    allSites SitePrefix246.checkSite [false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false, true])
    join_111 join_120

theorem join_122 :
    allSites SitePrefix246.checkSite [true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true, true])
    block_133 block_134

theorem join_123 :
    allSites SitePrefix246.checkSite [false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false, true])
    block_132 join_122

theorem join_124 :
    allSites SitePrefix246.checkSite [false, true, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false, true])
    block_135 block_136

theorem join_125 :
    allSites SitePrefix246.checkSite [true, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true, true])
    join_124 block_137

theorem join_126 :
    allSites SitePrefix246.checkSite [false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false, true])
    join_123 join_125

theorem join_127 :
    allSites SitePrefix246.checkSite [false, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false, true])
    block_138 block_139


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
