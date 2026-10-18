import BusyBeaver.ZFC.ProgramRouting245
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRouting245
import BusyBeaver.ZFC.SitesRouting245Cut219
import BusyBeaver.ZFC.SitesRouting245Join012
import BusyBeaver.ZFC.SitesRouting245Cut223
import BusyBeaver.ZFC.SitesRouting245Cut224
import BusyBeaver.ZFC.SitesRouting245Cut222
import BusyBeaver.ZFC.SitesRouting245Cut225
import BusyBeaver.ZFC.SitesRouting245Join000
import BusyBeaver.ZFC.SitesRouting245Cut226
import BusyBeaver.ZFC.SitesRouting245Cut227
import BusyBeaver.ZFC.SitesRouting245Batch001
import BusyBeaver.ZFC.SitesRouting245Cut228
import BusyBeaver.ZFC.SitesRouting245Cut229

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

theorem join_208 :
    allSites SiteRouting245.checkSite [false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_219 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_207

theorem join_209 :
    allSites SiteRouting245.checkSite [true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_223 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_224

theorem join_210 :
    allSites SiteRouting245.checkSite [false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_222 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_209

theorem join_211 :
    allSites SiteRouting245.checkSite [true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_210 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_225

theorem join_212 :
    allSites SiteRouting245.checkSite [true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_208 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_211

theorem join_213 :
    allSites SiteRouting245.checkSite [true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_206 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_212

theorem join_214 :
    allSites SiteRouting245.checkSite [true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_205 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_213

theorem join_215 :
    allSites SiteRouting245.checkSite [true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_201 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_214

theorem join_216 :
    allSites SiteRouting245.checkSite [true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_7 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_215

theorem join_217 :
    allSites SiteRouting245.checkSite [false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_5 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_216

theorem join_218 :
    allSites SiteRouting245.checkSite [true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_217 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_226

theorem join_219 :
    allSites SiteRouting245.checkSite [false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_1 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_218

theorem join_220 :
    allSites SiteRouting245.checkSite [true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_219 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_227

theorem join_221 :
    allSites SiteRouting245.checkSite [false, false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.block_5 SetTheory.BusyBeaver.ZFC.SitesRouting245.join_220

theorem join_222 :
    allSites SiteRouting245.checkSite [false, true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false]) = true :=
  allSites_join SiteRouting245.checkSite [false, true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_221 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_228

theorem join_223 :
    allSites SiteRouting245.checkSite [true, false, false, true, false, true, true, true]
      (descend TreeRouting245.tree [true, true, true, false, true, false, false, true]) = true :=
  allSites_join SiteRouting245.checkSite [true, false, false, true, false, true, true, true]
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, false])
    (descend TreeRouting245.tree [true, true, true, false, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRouting245.join_222 SetTheory.BusyBeaver.ZFC.SitesRouting245.block_229


end SetTheory.BusyBeaver.ZFC.SitesRouting245
