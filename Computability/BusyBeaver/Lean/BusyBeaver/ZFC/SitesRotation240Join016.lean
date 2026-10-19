import BusyBeaver.ZFC.TreeRotation240
import BusyBeaver.ZFC.SiteCoverage
import BusyBeaver.ZFC.SiteRotation240
import BusyBeaver.ZFC.SitesRotation240Batch269
import BusyBeaver.ZFC.SitesRotation240Join015
import BusyBeaver.ZFC.SitesRotation240Batch272
import BusyBeaver.ZFC.SitesRotation240Batch273
import BusyBeaver.ZFC.SitesRotation240Batch275
import BusyBeaver.ZFC.SitesRotation240Batch276
import BusyBeaver.ZFC.SitesRotation240Batch274
import BusyBeaver.ZFC.SitesRotation240Batch278
import BusyBeaver.ZFC.SitesRotation240Batch279
import BusyBeaver.ZFC.SitesRotation240Batch277
import BusyBeaver.ZFC.SitesRotation240Batch280
import BusyBeaver.ZFC.SitesRotation240Batch281
import BusyBeaver.ZFC.SitesRotation240Batch282
import BusyBeaver.ZFC.SitesRotation240Batch284
import BusyBeaver.ZFC.SitesRotation240Batch285
import BusyBeaver.ZFC.SitesRotation240Batch283

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

theorem join_256 :
    allSites SiteRotation240.checkSite [false, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_271 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_255

theorem join_257 :
    allSites SiteRotation240.checkSite [false, true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_274 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_275

theorem join_258 :
    allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_277 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_278

theorem join_259 :
    allSites SiteRotation240.checkSite [true, true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_276 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_258

theorem join_260 :
    allSites SiteRotation240.checkSite [true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_257 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_259

theorem join_261 :
    allSites SiteRotation240.checkSite [false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_256 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_260

theorem join_262 :
    allSites SiteRotation240.checkSite [true, false, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_280 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_281

theorem join_263 :
    allSites SiteRotation240.checkSite [false, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_279 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_262

theorem join_264 :
    allSites SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, false, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, false, true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, false, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_282 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_283

theorem join_265 :
    allSites SiteRotation240.checkSite [false, true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_264 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_284

theorem join_266 :
    allSites SiteRotation240.checkSite [true, true, true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_286 SetTheory.BusyBeaver.ZFC.SitesRotation240.block_287

theorem join_267 :
    allSites SiteRotation240.checkSite [true, true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.block_285 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_266

theorem join_268 :
    allSites SiteRotation240.checkSite [true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_265 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_267

theorem join_269 :
    allSites SiteRotation240.checkSite [true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_263 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_268

theorem join_270 :
    allSites SiteRotation240.checkSite [true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true]) = true :=
  allSites_join SiteRotation240.checkSite [true, false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_261 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_269

theorem join_271 :
    allSites SiteRotation240.checkSite [false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
      (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false]) = true :=
  allSites_join SiteRotation240.checkSite [false, true, false, true, true, false, false, true, false, true, false, true, false, true, true, false, true, false, true, false, false, true, false, false, true, false, true, true, true]
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, false])
    (descend TreeRotation240.tree [true, true, true, false, true, false, false, true, false, false, true, false, true, false, true, true, false, true, false, true, false, true, false, false, true, true, false, true, false, true])
    SetTheory.BusyBeaver.ZFC.SitesRotation240.join_254 SetTheory.BusyBeaver.ZFC.SitesRotation240.join_270


end SetTheory.BusyBeaver.ZFC.SitesRotation240
