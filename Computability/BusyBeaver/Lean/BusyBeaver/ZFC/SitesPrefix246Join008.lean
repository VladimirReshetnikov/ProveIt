import BusyBeaver.ZFC.ActualTree254
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SitePrefix246
import BusyBeaver.ZFC.SitesPrefix246Batch049
import BusyBeaver.ZFC.SitesPrefix246Batch050
import BusyBeaver.ZFC.SitesPrefix246Join007
import BusyBeaver.ZFC.SitesPrefix246Join006
import BusyBeaver.ZFC.SitesPrefix246Batch051
import BusyBeaver.ZFC.SitesPrefix246Batch052
import BusyBeaver.ZFC.SitesPrefix246Batch053
import BusyBeaver.ZFC.SitesPrefix246Batch054
import BusyBeaver.ZFC.SitesPrefix246Batch055

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

theorem join_128 :
    allSites SitePrefix246.checkSite [true, true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true, true, true])
    block_141 block_142

theorem join_129 :
    allSites SitePrefix246.checkSite [true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true, true])
    block_140 join_128

theorem join_130 :
    allSites SitePrefix246.checkSite [true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true, true])
    join_127 join_129

theorem join_131 :
    allSites SitePrefix246.checkSite [true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true, true])
    join_126 join_130

theorem join_132 :
    allSites SitePrefix246.checkSite [true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true, true])
    join_121 join_131

theorem join_133 :
    allSites SitePrefix246.checkSite [false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, false, true])
    join_110 join_132

theorem join_134 :
    allSites SitePrefix246.checkSite [false, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, false, true])
    block_143 block_144

theorem join_135 :
    allSites SitePrefix246.checkSite [false, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, false, true])
    block_145 block_146

theorem join_136 :
    allSites SitePrefix246.checkSite [false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false, true])
    join_135 block_147

theorem join_137 :
    allSites SitePrefix246.checkSite [true, false, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false, true, true])
    block_149 block_150

theorem join_138 :
    allSites SitePrefix246.checkSite [false, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false, true])
    block_148 join_137

theorem join_139 :
    allSites SitePrefix246.checkSite [true, true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, true, true])
    block_152 block_153

theorem join_140 :
    allSites SitePrefix246.checkSite [true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true, true])
    block_151 join_139

theorem join_141 :
    allSites SitePrefix246.checkSite [false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false]) = true :=
  allSites_join SitePrefix246.checkSite [false, true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false, true])
    join_138 join_140

theorem join_142 :
    allSites SitePrefix246.checkSite [true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true, true])
    join_141 block_154

theorem join_143 :
    allSites SitePrefix246.checkSite [true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true]) = true :=
  allSites_join SitePrefix246.checkSite [true, false, false, true, true, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, false])
    (descend ActualTree254.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true, true, false, false, true, true])
    join_136 join_142


end SetTheory.BusyBeaver.ZFC.SitesPrefix246
