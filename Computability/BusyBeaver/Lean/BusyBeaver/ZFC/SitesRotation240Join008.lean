import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Join007
import BusyBeaver.ZFC.SitesRotation240Join006
import BusyBeaver.ZFC.SitesRotation240Batch148
import BusyBeaver.ZFC.SitesRotation240Batch149
import BusyBeaver.ZFC.SitesRotation240Batch150
import BusyBeaver.ZFC.SitesRotation240Batch151
import BusyBeaver.ZFC.SitesRotation240Batch152
import BusyBeaver.ZFC.SitesRotation240Batch153
import BusyBeaver.ZFC.SitesRotation240Batch154
import BusyBeaver.ZFC.SitesRotation240Batch155
import BusyBeaver.ZFC.SitesRotation240Batch156
import BusyBeaver.ZFC.SitesRotation240Batch157
import BusyBeaver.ZFC.SitesRotation240Batch158
import BusyBeaver.ZFC.SitesRotation240Batch159
import BusyBeaver.ZFC.SitesRotation240Batch160
import BusyBeaver.ZFC.SitesRotation240Batch161

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

theorem join_128 :
    allSites SiteRotation240.checkSite [true, true, false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_120 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_127

theorem join_129 :
    allSites SiteRotation240.checkSite [true, false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_116 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_128

theorem join_130 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_110 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_129

theorem join_131 :
    allSites SiteRotation240.checkSite [false, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_150 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_151

theorem join_132 :
    allSites SiteRotation240.checkSite [false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_152 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_153

theorem join_133 :
    allSites SiteRotation240.checkSite [false, true, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_154 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_155

theorem join_134 :
    allSites SiteRotation240.checkSite [true, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_133 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_156

theorem join_135 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_132 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_134

theorem join_136 :
    allSites SiteRotation240.checkSite [false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_131 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_135

theorem join_137 :
    allSites SiteRotation240.checkSite [false, false, false, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_157 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_158

theorem join_138 :
    allSites SiteRotation240.checkSite [false, false, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_137 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_159

theorem join_139 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_138 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_160

theorem join_140 :
    allSites SiteRotation240.checkSite [false, true, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_161 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_162

theorem join_141 :
    allSites SiteRotation240.checkSite [true, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_140 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_163

theorem join_142 :
    allSites SiteRotation240.checkSite [true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_139 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_141

theorem join_143 :
    allSites SiteRotation240.checkSite [false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, true, true, true, false, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, false, true, true, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_136 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_142


end SetTheory.BusyBeaver.ZFC.SitesRotation240
