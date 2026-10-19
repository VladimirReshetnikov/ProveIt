import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Join013
import BusyBeaver.ZFC.SitesRotation240Batch238
import BusyBeaver.ZFC.SitesRotation240Batch239
import BusyBeaver.ZFC.SitesRotation240Batch240
import BusyBeaver.ZFC.SitesRotation240Batch241
import BusyBeaver.ZFC.SitesRotation240Batch242
import BusyBeaver.ZFC.SitesRotation240Batch243
import BusyBeaver.ZFC.SitesRotation240Batch244
import BusyBeaver.ZFC.SitesRotation240Batch245
import BusyBeaver.ZFC.SitesRotation240Batch246
import BusyBeaver.ZFC.SitesRotation240Batch247
import BusyBeaver.ZFC.SitesRotation240Batch248
import BusyBeaver.ZFC.SitesRotation240Batch249
import BusyBeaver.ZFC.SitesRotation240Batch250
import BusyBeaver.ZFC.SitesRotation240Batch251
import BusyBeaver.ZFC.SitesRotation240Batch252
import BusyBeaver.ZFC.SitesRotation240Batch253
import BusyBeaver.ZFC.SitesRotation240Batch254
import BusyBeaver.ZFC.SitesRotation240Batch255

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

theorem join_224 :
    allSites SiteRotation240.checkSite [false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_217 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_223

theorem join_225 :
    allSites SiteRotation240.checkSite [false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_240 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_241

theorem join_226 :
    allSites SiteRotation240.checkSite [false, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_242 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_243

theorem join_227 :
    allSites SiteRotation240.checkSite [false, true, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_244 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_245

theorem join_228 :
    allSites SiteRotation240.checkSite [true, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_227 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_246

theorem join_229 :
    allSites SiteRotation240.checkSite [true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_226 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_228

theorem join_230 :
    allSites SiteRotation240.checkSite [false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_225 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_229

theorem join_231 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_247 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_248

theorem join_232 :
    allSites SiteRotation240.checkSite [false, true, true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_249 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_250

theorem join_233 :
    allSites SiteRotation240.checkSite [true, true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_232 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_251

theorem join_234 :
    allSites SiteRotation240.checkSite [true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_231 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_233

theorem join_235 :
    allSites SiteRotation240.checkSite [false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_230 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_234

theorem join_236 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_252 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_253

theorem join_237 :
    allSites SiteRotation240.checkSite [true, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_254 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_255

theorem join_238 :
    allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_236 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_237

theorem join_239 :
    allSites SiteRotation240.checkSite [false, true, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, true, false, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, false, true, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_256 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_257


end SetTheory.BusyBeaver.ZFC.SitesRotation240
