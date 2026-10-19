import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Batch191
import BusyBeaver.ZFC.SitesRotation240Batch192
import BusyBeaver.ZFC.SitesRotation240Batch193
import BusyBeaver.ZFC.SitesRotation240Batch194
import BusyBeaver.ZFC.SitesRotation240Batch195
import BusyBeaver.ZFC.SitesRotation240Batch196
import BusyBeaver.ZFC.SitesRotation240Join010
import BusyBeaver.ZFC.SitesRotation240Batch199
import BusyBeaver.ZFC.SitesRotation240Batch200
import BusyBeaver.ZFC.SitesRotation240Batch198
import BusyBeaver.ZFC.SitesRotation240Batch197
import BusyBeaver.ZFC.SitesRotation240Batch201
import BusyBeaver.ZFC.SitesRotation240Batch202
import BusyBeaver.ZFC.SitesRotation240Batch203
import BusyBeaver.ZFC.SitesRotation240Batch204
import BusyBeaver.ZFC.SitesRotation240Batch206
import BusyBeaver.ZFC.SitesRotation240Batch207
import BusyBeaver.ZFC.SitesRotation240Batch205

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

theorem join_176 :
    allSites SiteRotation240.checkSite [false, false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_193 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_194

theorem join_177 :
    allSites SiteRotation240.checkSite [true, false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_195 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_196

theorem join_178 :
    allSites SiteRotation240.checkSite [false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_176 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_177

theorem join_179 :
    allSites SiteRotation240.checkSite [true, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_197 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_198

theorem join_180 :
    allSites SiteRotation240.checkSite [true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_178 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_179

theorem join_181 :
    allSites SiteRotation240.checkSite [true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_175 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_180

theorem join_182 :
    allSites SiteRotation240.checkSite [false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_169 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_181

theorem join_183 :
    allSites SiteRotation240.checkSite [true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_201 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_202

theorem join_184 :
    allSites SiteRotation240.checkSite [true, false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_200 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_183

theorem join_185 :
    allSites SiteRotation240.checkSite [false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_199 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_184

theorem join_186 :
    allSites SiteRotation240.checkSite [false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_203 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_204

theorem join_187 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_186 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_205

theorem join_188 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_185 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_187

theorem join_189 :
    allSites SiteRotation240.checkSite [false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_188 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_206

theorem join_190 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_208 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_209

theorem join_191 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, true, true, false, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, false, true, true, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_207 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_190


end SetTheory.BusyBeaver.ZFC.SitesRotation240
